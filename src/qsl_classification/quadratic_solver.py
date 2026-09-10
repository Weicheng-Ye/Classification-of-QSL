"""Exact solutions of Boolean quadratic constraints.

Linear equations are eliminated before branching. Every leaf is an affine
space, whose solutions are reconstructed in the original H² coordinates.
This avoids scanning the 2^28 candidates of pmm with toric-code coefficients.
"""
from collections import Counter
import numpy as np
from .indicators import QuadraticIndicators


def binary_encoding(model, orders):
    """Expand cyclic 2-power factors; binomial(n,2) is the second bit of n."""
    offsets=[]
    rank=0
    for order in orders:
        order=int(order)
        if order < 2 or order & (order-1):
            raise ValueError('Binary encoding requires cyclic 2-power factors')
        offsets.append(rank)
        rank += order.bit_length()-1
    linear=np.zeros((rank,len(model.base)),dtype=np.uint8)
    for i,offset in enumerate(offsets):
        linear[offset] ^= model.linear[i]
    pairs=[]
    quadratics=[]
    for (i,j),values in zip(model.pairs,model.quad):
        if i == j:
            if orders[i] > 2:
                linear[offsets[i]+1] ^= values
            elif values.any():
                raise ArithmeticError('An order-two coordinate failed periodicity')
        else:
            pairs.append((offsets[i],offsets[j]))
            quadratics.append(values)
    return QuadraticIndicators(model.base,linear,pairs,quadratics)


def binary_solutions(model, target):
    rank = len(model.linear)
    equations = []
    for j,b in enumerate(model.base):
        polynomial = {0} if b != target[j] else set()
        polynomial.update(1<<i for i,v in enumerate(model.linear) if v[j])
        for (i,k),values in zip(model.pairs,model.quad):
            if values[j]:
                if i == k:
                    raise ArithmeticError('A binary coordinate has nonperiodic diagonal polarization')
                term=(1<<i)|(1<<k)
                polynomial.symmetric_difference_update((term,))
        if polynomial:
            equations.append(frozenset(polynomial))

    def solve(equations, variables, relations):
        equations=set(equations)
        while equations:
            if frozenset((0,)) in equations:
                return
            linear = next((p for p in equations if all(t.bit_count() <= 1 for t in p)),None)
            if linear is None:
                break
            mask = sum(t for t in linear if t)
            pivot = mask & -mask
            expression = set(linear)-{pivot}
            relations=relations+[(pivot,mask ^ pivot,int(0 in linear))]
            variables ^= pivot
            replaced=set()
            for polynomial in equations:
                terms=set(polynomial)
                for term in polynomial:
                    if term & pivot:
                        terms.remove(term)
                        other=term ^ pivot
                        for t in expression:
                            replacement=other | t
                            terms.symmetric_difference_update((replacement,))
                if terms:
                    replaced.add(frozenset(terms))
            equations=replaced
        if not equations:
            free=[]
            mask=variables
            while mask:
                bit=mask & -mask
                free.append(bit)
                mask^=bit
            for assignment in range(1<<len(free)):
                bits=sum(bit for i,bit in enumerate(free) if assignment>>i & 1)
                for pivot,mask,constant in reversed(relations):
                    if (bits & mask).bit_count() % 2 ^ constant:
                        bits |= pivot
                yield bits
            return
        occurrences=Counter()
        for polynomial in equations:
            for term in polynomial:
                if term.bit_count()==2:
                    bit=term & -term
                    occurrences[bit]+=1
                    occurrences[term ^ bit]+=1
        pivot=max(occurrences,key=occurrences.get)
        for value in (0,1):
            equation=frozenset((pivot,0)) if value else frozenset((pivot,))
            yield from solve(equations | {equation},variables,relations)
    yield from solve(equations,(1<<rank)-1,[])
