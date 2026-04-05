def mod2(x):
    if isinstance(x, list):
        return [item % 2 for item in x]
    return x % 2

def addList(A, B):
    return [x + y for x, y in zip(A, B)]

def _int_digits(val, pad):
    return [int(x) for x in bin(val)[2:].zfill(pad)]

def IndicatorZ2T(g, Action, SF, ActionGenerate, SFGenerate):
    flag = ActionGenerate(g, Action)
    Ind = 0
    if flag == 0:
        s = SFGenerate(g, g, Action, SF)
        Ind = mod2(s[0] * s[1])
    return Ind

def IndicatorZ2TZ2T(g1, g2, Action, SF, ActionGenerate, SFGenerate):
    flag1 = ActionGenerate(g1, Action)
    flag2 = ActionGenerate(g2, Action)
    Ind = 0
    if flag1 == 0 and flag2 == 0:
        s = SFGenerate(g1, g1, Action, SF)
        t = SFGenerate(g2, g2, Action, SF)
        st = addList(SFGenerate(g1, g2, Action, SF), SFGenerate(g2, g1, Action, SF))
        Ind = mod2(s[0]*t[1] + s[1]*t[0] + st[0]*st[1])
    if flag1 == 1 and flag2 == 0:
        t = SFGenerate(g2, g2, Action, SF)
        Ind = mod2(t[0])
    if flag1 == 0 and flag2 == 1:
        t = SFGenerate(g1, g1, Action, SF)
        Ind = mod2(t[0])
    if flag1 == 1 and flag2 == 1:
        st = addList(addList(SFGenerate(g1, g1, Action, SF), SFGenerate(g2, g2, Action, SF)),
                     addList(SFGenerate(g1, g2, Action, SF), SFGenerate(g2, g1, Action, SF)))
        Ind = mod2(st[0])
    return Ind

def IndicatorSO3(Action, SF, SFGenerate):
    s = SFGenerate([0,0,0,0,0,1], [0,0,0,0,0,1], Action, SF)
    Ind = mod2(s[0]*s[1])
    return Ind

def IndicatorZ2(g, Action, SF, ActionGenerate, SFGenerate):
    flag = ActionGenerate(g, Action)
    Ind = 0
    if flag == 0:
        st = SFGenerate([0,0,0,0,0,1], [0,0,0,0,0,1], Action, SF)
        s = SFGenerate(g, g, Action, SF)
        Ind = mod2(s[0]*st[1] + s[1]*st[0])
    return Ind

def p6mBxy(g1, g2):
    if g1[2]%6 == 0 and g1[3]%2 == 0:
        return g1[1]*g2[0]
    elif g1[2]%6 == 1 and g1[3]%2 == 0:
        return g2[0]*(g2[0]-1)//2 - g2[1]*g2[0] + g1[1]*(g2[0]-g2[1])
    elif g1[2]%6 == 2 and g1[3]%2 == 0:
        return g2[1]*(g2[1]+1)//2 - g2[0] - g2[1]*(g1[1]+g2[0])
    elif g1[2]%6 == 3 and g1[3]%2 == 0:
        return -g2[0] + g2[1] - g1[1]*g2[0]
    elif g1[2]%6 == 4 and g1[3]%2 == 0:
        return g2[0]*(g2[0]-1)//2 + g2[1] - g2[0]*g1[1] + g2[1]*(g1[1]-g2[0])
    elif g1[2]%6 == 5 and g1[3]%2 == 0:
        return g2[1]*(g2[1]+1)//2 + g2[1]*(g1[1]-g2[0])
    elif g1[2]%6 == 0 and g1[3]%2 == 1:
        return (g1[1]+g2[0])*g2[1]
    elif g1[2]%6 == 1 and g1[3]%2 == 1:
        return g2[1]*(g2[1]-1)//2 + g1[1]*(-g2[0]+g2[1])
    elif g1[2]%6 == 2 and g1[3]%2 == 1:
        return g2[0]*(g2[0]+1)//2 - g2[1] - g2[0]*g1[1]
    elif g1[2]%6 == 3 and g1[3]%2 == 1:
        return g2[0] - g2[1] - (g1[1]-g2[0])*g2[1]
    elif g1[2]%6 == 4 and g1[3]%2 == 1:
        return g2[1]*(g2[1]-1)//2 + g2[0] + g1[1]*(g2[0]-g2[1])
    elif g1[2]%6 == 5 and g1[3]%2 == 1:
        return g2[0]*(g2[0]+1)//2 + g2[0]*g1[1]


def p6mO3ActionGenerate(g, Action):
    return (g[2]*Action[0] + g[3]*Action[1] + g[4]*Action[2]) % 2

def p6mO3SFGenerate(g1, g2, Action, SF):
    if Action[0] == 0 and Action[1] == 0 and Action[2] == 0:
        res = [
            p6mBxy(g1, g2)*SF[0][0] + g1[2]*g2[2]*SF[0][1] + g1[2]*g2[3]*SF[0][2] + g1[3]*g2[3]*SF[0][3] + g1[2]*g2[4]*SF[0][4] + g1[3]*g2[4]*SF[0][5] + g1[4]*g2[4]*SF[0][6] + g1[5]*g2[5]*SF[0][7],
            p6mBxy(g1, g2)*SF[1][0] + g1[2]*g2[2]*SF[1][1] + g1[2]*g2[3]*SF[1][2] + g1[3]*g2[3]*SF[1][3] + g1[2]*g2[4]*SF[1][4] + g1[3]*g2[4]*SF[1][5] + g1[4]*g2[4]*SF[1][6] + g1[5]*g2[5]*SF[1][7]
        ]
    elif Action[2] == 1:
        res = [
            p6mBxy(g1, g2)*SF[0] + g1[2]*g2[2]*SF[1] + g1[2]*g2[3]*SF[2] + g1[3]*g2[3]*SF[3] + g1[5]*g2[5]*SF[4],
            p6mBxy(g1, g2)*SF[0] + g1[2]*g2[2]*SF[1] + g1[2]*g2[3]*SF[2] + g1[3]*g2[3]*SF[3] + g1[5]*g2[5]*SF[4]
        ]
    elif Action[0] == 0 and Action[1] == 1 and Action[2] == 0:
        res = [
            p6mBxy(g1, g2)*SF[0] + g1[2]*g2[2]*SF[1] + g1[2]*g2[4]*SF[2] + g1[4]*g2[4]*SF[3] + g1[5]*g2[5]*SF[4],
            p6mBxy(g1, g2)*SF[0] + g1[2]*g2[2]*SF[1] + g1[2]*g2[4]*SF[2] + g1[4]*g2[4]*SF[3] + g1[5]*g2[5]*SF[4]
        ]
    elif Action[0] == 1 and Action[2] == 0:
        res = [
            p6mBxy(g1, g2)*SF[0] + g1[3]*g2[3]*SF[1] + g1[3]*g2[4]*SF[2] + g1[4]*g2[4]*SF[3] + g1[5]*g2[5]*SF[4],
            p6mBxy(g1, g2)*SF[0] + g1[3]*g2[3]*SF[1] + g1[3]*g2[4]*SF[2] + g1[4]*g2[4]*SF[3] + g1[5]*g2[5]*SF[4]
        ]
    return mod2(res)

def p6mO3Multiply(Action, SF):
    return [
        IndicatorZ2T([0,0,0,0,1,0], Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate),
        IndicatorZ2T([0,0,0,1,0,0], Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate),
        IndicatorZ2T([0,0,3,0,1,0], Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate),
        IndicatorZ2T([0,0,3,1,0,0], Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate),
        IndicatorZ2TZ2T([0,0,0,0,1,0], [0,0,3,0,1,0], Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate),
        IndicatorZ2TZ2T([0,0,0,0,1,0], [0,0,0,1,0,0], Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate),
        IndicatorZ2TZ2T([0,0,0,1,0,0], [0,0,3,0,1,0], Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate),
        IndicatorZ2TZ2T([0,0,3,0,1,0], [0,0,3,1,0,0], Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate),
        IndicatorZ2TZ2T([0,0,0,1,0,0], [0,0,3,1,0,0], Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate),
        IndicatorZ2T([1,1,3,0,1,0], Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate),
        IndicatorZ2TZ2T([0,0,0,1,0,0], [1,1,3,0,1,0], Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate),
        IndicatorZ2TZ2T([0,0,0,0,1,0], [1,1,3,0,1,0], Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate),
        IndicatorZ2TZ2T([0,0,0,1,0,0], [1,1,3,1,0,0], Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate),
        IndicatorZ2T([0,0,0,0,1,1], Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate),
        IndicatorZ2T([0,0,0,1,0,1], Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate),
        IndicatorZ2T([0,0,3,0,1,1], Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate),
        IndicatorZ2T([0,0,3,1,0,1], Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate),
        IndicatorZ2T([1,1,3,0,1,1], Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate),
        IndicatorSO3(Action, SF, p6mO3SFGenerate),
        IndicatorZ2([0,0,3,0,0,0], Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate),
        IndicatorZ2([0,0,0,1,1,0], Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate)
    ]

p6mO3Anomaly0 = [0]*21
p6mO3Anomalya = [0]*21; p6mO3Anomalya[2] = 1; p6mO3Anomalya[4] = 1; p6mO3Anomalya[19] = 1
p6mO3Anomalyc = [0]*21; p6mO3Anomalyc[9] = 1; p6mO3Anomalyc[11] = 1
p6mO3Anomalyac = mod2(addList(p6mO3Anomalya, p6mO3Anomalyc))

def get_p6mO3_ActionList(Action):
    if Action == 1: return [0, 0, 0]
    elif 2 <= Action <= 5: return _int_digits(Action - 2, 2) + [1]
    elif 6 <= Action <= 8: return _int_digits(Action - 5, 2) + [0]

def p6mO3Generate(Action, homotopylist):
    result = [[] for _ in range(len(homotopylist))]
    matchinganomaly = []
    
    for h in homotopylist:
        if h == "0": matchinganomaly.append(p6mO3Anomaly0)
        elif h == "a": matchinganomaly.append(p6mO3Anomalya)
        elif h == "c": matchinganomaly.append(p6mO3Anomalyc)
        elif h == "a+c": matchinganomaly.append(p6mO3Anomalyac)
        
    ActionList = get_p6mO3_ActionList(Action)

    if Action == 1:
        for i in range(2**8):
            for j in range(i + 1):
                SFCe = _int_digits(i, 8)
                SFCm = _int_digits(j, 8)
                Anomaly = p6mO3Multiply(ActionList, [SFCe, SFCm])
                for k in range(len(homotopylist)):
                    if Anomaly == matchinganomaly[k]:
                        result[k].append(SFCe + SFCm)
                        break
    elif Action > 1:
        for i in range(2**5):
            SFCe = _int_digits(i, 5)
            Anomaly = p6mO3Multiply(ActionList, SFCe)
            for k in range(len(homotopylist)):
                if Anomaly == matchinganomaly[k]:
                    result[k].append(SFCe)
                    break
    return result

def p6mO3CheckSF(Action, SF):
    ActionList = get_p6mO3_ActionList(Action)
    if Action == 1:
        Anomaly = p6mO3Multiply(ActionList, [SF[0:8], SF[8:16]])
    else:
        Anomaly = p6mO3Multiply(ActionList, SF)
        
    if Anomaly == p6mO3Anomaly0: return "0"
    elif Anomaly == p6mO3Anomalya: return "a"
    elif Anomaly == p6mO3Anomalyc: return "c"
    elif Anomaly == p6mO3Anomalyac: return "a+c"
    return "empty"


def p6mZ2ActionGenerate(g, Action):
    return (g[2]*Action[0] + g[3]*Action[1] + g[4]*Action[2]) % 2

def p6mZ2SFGenerate(g1, g2, Action, SF):
    if Action[0] == 0 and Action[1] == 0 and Action[2] == 0:
        res = [
            p6mBxy(g1, g2)*SF[0][0] + g1[2]*g2[2]*SF[0][1] + g1[2]*g2[3]*SF[0][2] + g1[3]*g2[3]*SF[0][3] + g1[2]*g2[4]*SF[0][4] + g1[3]*g2[4]*SF[0][5] + g1[4]*g2[4]*SF[0][6],
            p6mBxy(g1, g2)*SF[1][0] + g1[2]*g2[2]*SF[1][1] + g1[2]*g2[3]*SF[1][2] + g1[3]*g2[3]*SF[1][3] + g1[2]*g2[4]*SF[1][4] + g1[3]*g2[4]*SF[1][5] + g1[4]*g2[4]*SF[1][6]
        ]
    elif Action[2] == 1:
        res = [
            p6mBxy(g1, g2)*SF[0] + g1[2]*g2[2]*SF[1] + g1[2]*g2[3]*SF[2] + g1[3]*g2[3]*SF[3],
            p6mBxy(g1, g2)*SF[1] + g1[2]*g2[2]*SF[1] + g1[2]*g2[3]*SF[2] + g1[3]*g2[3]*SF[3] # Error in original? Wait!
        ] # wait, looking at Z2TO.m line 171
        # p6mBxy[g1,g2]*{SF[[1]],SF[[1]]}+g1[[3]]*g2[[3]]*{SF[[2]],SF[[2]]}+g1[[3]]*g2[[4]]*{SF[[3]],SF[[3]]}+g1[[4]]*g2[[4]]*{SF[[4]],SF[[4]]}
        res = [
            p6mBxy(g1, g2)*SF[0] + g1[2]*g2[2]*SF[1] + g1[2]*g2[3]*SF[2] + g1[3]*g2[3]*SF[3],
            p6mBxy(g1, g2)*SF[0] + g1[2]*g2[2]*SF[1] + g1[2]*g2[3]*SF[2] + g1[3]*g2[3]*SF[3]
        ]
    elif Action[0] == 0 and Action[1] == 1 and Action[2] == 0:
        res = [
            p6mBxy(g1, g2)*SF[0] + g1[2]*g2[2]*SF[1] + g1[2]*g2[4]*SF[2] + g1[4]*g2[4]*SF[3],
            p6mBxy(g1, g2)*SF[0] + g1[2]*g2[2]*SF[1] + g1[2]*g2[4]*SF[2] + g1[4]*g2[4]*SF[3]
        ]
    elif Action[0] == 1 and Action[2] == 0:
        res = [
            p6mBxy(g1, g2)*SF[0] + g1[3]*g2[3]*SF[1] + g1[3]*g2[4]*SF[2] + g1[4]*g2[4]*SF[3],
            p6mBxy(g1, g2)*SF[0] + g1[3]*g2[3]*SF[1] + g1[3]*g2[4]*SF[2] + g1[4]*g2[4]*SF[3]
        ]
    return mod2(res)

def p6mZ2Multiply(Action, SF):
    return [
        IndicatorZ2T([0,0,0,0,1,0], Action, SF, p6mZ2ActionGenerate, p6mZ2SFGenerate),
        IndicatorZ2T([0,0,0,1,0,0], Action, SF, p6mZ2ActionGenerate, p6mZ2SFGenerate),
        IndicatorZ2T([0,0,3,0,1,0], Action, SF, p6mZ2ActionGenerate, p6mZ2SFGenerate),
        IndicatorZ2T([0,0,3,1,0,0], Action, SF, p6mZ2ActionGenerate, p6mZ2SFGenerate),
        IndicatorZ2TZ2T([0,0,0,0,1,0], [0,0,3,0,1,0], Action, SF, p6mZ2ActionGenerate, p6mZ2SFGenerate),
        IndicatorZ2TZ2T([0,0,0,0,1,0], [0,0,0,1,0,0], Action, SF, p6mZ2ActionGenerate, p6mZ2SFGenerate),
        IndicatorZ2TZ2T([0,0,0,1,0,0], [0,0,3,0,1,0], Action, SF, p6mZ2ActionGenerate, p6mZ2SFGenerate),
        IndicatorZ2TZ2T([0,0,3,0,1,0], [0,0,3,1,0,0], Action, SF, p6mZ2ActionGenerate, p6mZ2SFGenerate),
        IndicatorZ2TZ2T([0,0,0,1,0,0], [0,0,3,1,0,0], Action, SF, p6mZ2ActionGenerate, p6mZ2SFGenerate),
        IndicatorZ2T([1,1,3,0,1,0], Action, SF, p6mZ2ActionGenerate, p6mZ2SFGenerate),
        IndicatorZ2TZ2T([0,0,0,1,0,0], [1,1,3,0,1,0], Action, SF, p6mZ2ActionGenerate, p6mZ2SFGenerate),
        IndicatorZ2TZ2T([0,0,0,0,1,0], [1,1,3,0,1,0], Action, SF, p6mZ2ActionGenerate, p6mZ2SFGenerate),
        IndicatorZ2TZ2T([0,0,0,1,0,0], [1,1,3,1,0,0], Action, SF, p6mZ2ActionGenerate, p6mZ2SFGenerate)
    ]

p6mZ2Anomaly0 = [0]*13
p6mZ2Anomalya = [0]*13; p6mZ2Anomalya[2] = 1; p6mZ2Anomalya[4] = 1
p6mZ2Anomalyc = [0]*13; p6mZ2Anomalyc[9] = 1; p6mZ2Anomalyc[11] = 1
p6mZ2Anomalyac = mod2(addList(p6mZ2Anomalya, p6mZ2Anomalyc))

def p6mZ2Generate(Action, homotopylist):
    result = [[] for _ in range(len(homotopylist))]
    matchinganomaly = []
    
    for h in homotopylist:
        if h == "0": matchinganomaly.append(p6mZ2Anomaly0)
        elif h == "a": matchinganomaly.append(p6mZ2Anomalya)
        elif h == "c": matchinganomaly.append(p6mZ2Anomalyc)
        elif h == "a+c": matchinganomaly.append(p6mZ2Anomalyac)
        
    ActionList = get_p6mO3_ActionList(Action)

    if Action == 1:
        for i in range(2**7):
            for j in range(i + 1):
                SFCe = _int_digits(i, 7)
                SFCm = _int_digits(j, 7)
                Anomaly = p6mZ2Multiply(ActionList, [SFCe, SFCm])
                for k in range(len(homotopylist)):
                    if Anomaly == matchinganomaly[k]:
                        result[k].append(SFCe + SFCm)
                        break
    elif Action > 1:
        for i in range(2**4):
            SFCe = _int_digits(i, 4)
            Anomaly = p6mZ2Multiply(ActionList, SFCe)
            for k in range(len(homotopylist)):
                if Anomaly == matchinganomaly[k]:
                    result[k].append(SFCe)
                    break
    return result

def p6mZ2CheckSF(Action, SF):
    ActionList = get_p6mO3_ActionList(Action)
    if Action == 1:
        Anomaly = p6mZ2Multiply(ActionList, [SF[0:7], SF[7:14]])
    else:
        Anomaly = p6mZ2Multiply(ActionList, SF)
        
    if Anomaly == p6mZ2Anomaly0: return "0"
    elif Anomaly == p6mZ2Anomalya: return "a"
    elif Anomaly == p6mZ2Anomalyc: return "c"
    elif Anomaly == p6mZ2Anomalyac: return "a+c"
    return "empty"


def p4mBxy(g1, g2):
    if g1[2]%2 == 0:
        return g1[1]*g2[0]
    else:
        return (g1[1] + g2[0])*g2[1]

def p4mBc2(g1, g2):
    val = g1[2] + (-1)**(g1[3]) * g2[2]
    return (val - (val % 4)) // 4

def Flip(w):
    return [w[1], w[0]]

def p4maction1wasym1(g1, g2):
    return [g1[0]*g2[3], g1[1]*g2[3]]

def p4maction1wasym2(g1, g2):
    return [
        (g1[2]//2 + g1[2]%2 + g1[2]*g1[3]) * g2[3],
        (g1[2]//2 + g1[3] + g1[2]*g1[3]) * g2[3]
    ]

def p4maction1wasym3(g1, g2):
    return [
        (g1[2]//2 + g1[2]%2 + g1[2]*g1[3]) * ((1-g1[2])*g2[0] + g1[2]*g2[1]),
        (g1[2]//2 + g1[3] + g1[2]*g1[3]) * ((1-g1[2])*g2[1] + g1[2]*g2[0])
    ]

def p4maction1wasym4(g1, g2):
    return [g1[0]*g2[4], g1[1]*g2[4]]

def p4maction1wasym5(g1, g2):
    return [
        (g1[2]//2 + g1[2]%2 + g1[2]*g1[3]) * g2[4],
        (g1[2]//2 + g1[3] + g1[2]*g1[3]) * g2[4]
    ]

def p4maction2wasym1(g1, g2):
    return [
        (g1[2]//2) * ((1 - (g1[2]+g1[3])) * (g2[2]//2) + (g1[2]+g1[3]) * (g2[2]//2 + g2[2]%2)),
        (g1[2]//2 + g1[2]%2) * ((1 - (g1[2]+g1[3])) * (g2[2]//2 + g2[2]%2) + (g1[2]+g1[3]) * (g2[2]//2))
    ]

def p4maction2wasym2(g1, g2):
    return [
        (g1[2]//2) * g2[4],
        (g1[2]//2 + g1[2]%2) * g2[4]
    ]

def _p4maction3_Inv(g):
    return [
        (g[0] + g[1] + ((g[0]+g[1])%2) * (-1)**(g[2]//2 + g[3])) // 2,
        (-g[0] + g[1] - ((g[0]+g[1])%2) * (-1)**(g[2]//2 + g[2]%2 + g[3])) // 2,
        (g[2] - (g[3]+g[0]+g[1])%2) % 4,
        (g[3]+g[0]+g[1]) % 2
    ]

def _p4maction3_Trans(g):
    if g[2]==0 and g[3]==0: return [g[1], g[0], 0, 0]
    elif g[2]==1 and g[3]==0: return [g[1]+1, g[0], 3, 0]
    elif g[2]==2 and g[3]==0: return [g[1]+1, g[0]-1, 2, 0]
    elif g[2]==3 and g[3]==0: return [g[1], g[0]-1, 1, 0]
    elif g[2]==0 and g[3]==1: return [g[1], g[0]-1, 2, 1]
    elif g[2]==1 and g[3]==1: return [g[1], g[0], 1, 1]
    elif g[2]==2 and g[3]==1: return [g[1]+1, g[0], 0, 1]
    elif g[2]==3 and g[3]==1: return [g[1]+1, g[0]-1, 3, 1]
    
def p4maction3wasym1(g1, g2):
    inv1 = _p4maction3_Inv(g1)
    inv2 = _p4maction3_Inv(g2)
    if (g1[0] + g1[1]) % 2 == 0:
        return [p4mBxy(inv1, inv2), p4mBxy(_p4maction3_Trans(inv1), _p4maction3_Trans(inv2))]
    else:
        return [p4mBxy(inv1, _p4maction3_Trans(inv2)), p4mBxy(_p4maction3_Trans(inv1), inv2)]

def p4maction3wasym2(g1, g2):
    factor1_1 = g1[1] + (g1[0]+g1[1])*g1[2]
    factor1_2 = g1[1] + (g1[0]+g1[1])*g1[2] + g1[2]
    term1 = g2[1] + (g2[0]+g2[1])*g2[2]
    term2 = g2[1] + (g2[0]+g2[1])*g2[2] + g2[2]
    f1 = factor1_1 * ((1 - (g1[0]+g1[1])) * term1 + (g1[0]+g1[1]) * term2)
    f2 = factor1_2 * ((1 - (g1[0]+g1[1])) * term2 + (g1[0]+g1[1]) * term1)
    return [f1, f2]

def p4maction3wasym3(g1, g2):
    return [
        (g1[1] + (g1[0]+g1[1])*g1[2]) * g2[4],
        (g1[1] + (g1[0]+g1[1])*g1[2] + g1[2]) * g2[4]
    ]

def _p4maction4_Inv(g):
    res = []
    mod_val = (g[0]+g[1]+g[2]) % 2
    if g[2]==0 and mod_val==0: res.extend([(g[0]+g[1])//2, (-g[0]+g[1])//2])
    elif g[2]==1 and mod_val==0: res.extend([(g[0]+g[1]-1)//2, (-g[0]+g[1]+1)//2])
    elif g[2]==2 and mod_val==0: res.extend([(g[0]+g[1])//2-1, (-g[0]+g[1])//2])
    elif g[2]==3 and mod_val==0: res.extend([(g[0]+g[1]-1)//2, (-g[0]+g[1]-1)//2])
    elif g[2]==1 and mod_val==1: res.extend([(g[0]+g[1])//2-1, (-g[0]+g[1])//2])
    elif g[2]==2 and mod_val==1: res.extend([(g[0]+g[1]-1)//2, (-g[0]+g[1]-1)//2])
    elif g[2]==3 and mod_val==1: res.extend([(g[0]+g[1])//2, (-g[0]+g[1])//2])
    elif g[2]==0 and mod_val==1: res.extend([(g[0]+g[1]-1)//2, (-g[0]+g[1]+1)//2])
    res.extend([(g[2] - (g[2]+g[0]+g[1])%2) % 4, (g[2]+g[0]+g[1]) % 2])
    return res

def _p4maction4_Trans(g):
    if g[2]==0 and g[3]==0: return [g[1], g[0], 0, 0]
    elif g[2]==1 and g[3]==0: return [g[1]-1, g[0], 3, 0]
    elif g[2]==2 and g[3]==0: return [g[1]-1, g[0]+1, 2, 0]
    elif g[2]==3 and g[3]==0: return [g[1], g[0]+1, 1, 0]
    elif g[2]==0 and g[3]==1: return [g[1], g[0]+1, 2, 1]
    elif g[2]==1 and g[3]==1: return [g[1], g[0], 1, 1]
    elif g[2]==2 and g[3]==1: return [g[1]-1, g[0], 0, 1]
    elif g[2]==3 and g[3]==1: return [g[1]-1, g[0]+1, 3, 1]

def p4maction4wasym1(g1, g2):
    inv1 = _p4maction4_Inv(g1)
    inv2 = _p4maction4_Inv(g2)
    if (g1[0]+g1[1]+g1[2]+g1[3]) % 2 == 0:
        return [p4mBxy(inv1, inv2), p4mBxy(_p4maction4_Trans(inv1), _p4maction4_Trans(inv2))]
    else:
        return [p4mBxy(inv1, _p4maction4_Trans(inv2)), p4mBxy(_p4maction4_Trans(inv1), inv2)]

def p4maction4wasym2(g1, g2):
    factor1_1 = g1[1] + g1[2]//2 + (g1[0]+g1[1]+g1[2])*g1[2]
    factor1_2 = g1[1] + g1[2]//2 + (g1[0]+g1[1])*g1[2]
    term1 = g2[1] + g2[2]//2 + (g2[0]+g2[1]+g2[2])*g2[2]
    term2 = g2[1] + g2[2]//2 + (g2[0]+g2[1])*g2[2]
    mod_val = (g1[0]+g1[1]+g1[2]+g1[3])
    f1 = factor1_1 * ((1 - mod_val) * term1 + mod_val * term2)
    f2 = factor1_2 * ((1 - mod_val) * term2 + mod_val * term1)
    return [f1, f2]

def p4maction4wasym3(g1, g2):
    return [
        (g1[1] + g1[2]//2 + (g1[0]+g1[1]+g1[2])*g1[2]) * g2[4],
        (g1[1] + g1[2]//2 + (g1[0]+g1[1])*g1[2]) * g2[4]
    ]

def p4mO3ActionGenerate(g, Action):
    return ((g[0]+g[1])*Action[0] + g[2]*Action[1] + g[3]*Action[2] + g[4]*Action[3]) % 2

def p4mO3SFGenerate(g1, g2, Action, SF):
    if Action[0]==0 and Action[1]==0 and Action[2]==0 and Action[3]==0:
        return mod2([
            p4mBxy(g1, g2)*SF[0][0] + p4mBc2(g1, g2)*SF[0][1] + (g1[0]+g1[1])*(g2[0]+g2[1])*SF[0][2] +
            (g1[0]+g1[1])*g2[3]*SF[0][3] + g1[2]*g2[2]*SF[0][4] + g1[3]*g2[3]*SF[0][5] +
            (g1[0]+g1[1])*g2[4]*SF[0][6] + g1[2]*g2[4]*SF[0][7] + g1[3]*g2[4]*SF[0][8] +
            g1[4]*g2[4]*SF[0][9] + g1[5]*g2[5]*SF[0][10],
            p4mBxy(g1, g2)*SF[1][0] + p4mBc2(g1, g2)*SF[1][1] + (g1[0]+g1[1])*(g2[0]+g2[1])*SF[1][2] +
            (g1[0]+g1[1])*g2[3]*SF[1][3] + g1[2]*g2[2]*SF[1][4] + g1[3]*g2[3]*SF[1][5] +
            (g1[0]+g1[1])*g2[4]*SF[1][6] + g1[2]*g2[4]*SF[1][7] + g1[3]*g2[4]*SF[1][8] +
            g1[4]*g2[4]*SF[1][9] + g1[5]*g2[5]*SF[1][10]
        ])
    elif Action[3]==1:
        return mod2([
            p4mBxy(g1, g2)*SF[0] + p4mBc2(g1, g2)*SF[1] + (g1[0]+g1[1])*(g2[0]+g2[1])*SF[2] +
            (g1[0]+g1[1])*g2[3]*SF[3] + g1[2]*g2[2]*SF[4] + g1[3]*g2[3]*SF[5] + g1[5]*g2[5]*SF[6],
            p4mBxy(g1, g2)*SF[0] + p4mBc2(g1, g2)*SF[1] + (g1[0]+g1[1])*(g2[0]+g2[1])*SF[2] +
            (g1[0]+g1[1])*g2[3]*SF[3] + g1[2]*g2[2]*SF[4] + g1[3]*g2[3]*SF[5] + g1[5]*g2[5]*SF[6]
        ])
    elif Action[0]==0 and Action[1]==0 and Action[2]==1 and Action[3]==0:
        return mod2([
            p4mBxy(g1, g2)*SF[0] + p4mBc2(g1, g2)*SF[1] + (g1[0]+g1[1])*(g2[0]+g2[1])*SF[2] +
            (g1[0]+g1[1])*g2[4]*SF[3] + g1[2]*g2[4]*SF[4] + g1[4]*g2[4]*SF[5] + g1[5]*g2[5]*SF[6],
            p4mBxy(g1, g2)*SF[0] + p4mBc2(g1, g2)*SF[1] + (g1[0]+g1[1])*(g2[0]+g2[1])*SF[2] +
            (g1[0]+g1[1])*g2[4]*SF[3] + g1[2]*g2[4]*SF[4] + g1[4]*g2[4]*SF[5] + g1[5]*g2[5]*SF[6]
        ])
    elif Action[0]==0 and Action[1]==1 and Action[2]==0 and Action[3]==0:
        term4 = p4maction1wasym1(g1, g2); term5 = p4maction1wasym2(g1, g2); term6 = p4maction1wasym3(g1, g2); term7 = p4maction1wasym4(g1, g2); term8 = p4maction1wasym5(g1, g2)
        term9 = Flip(term4); term10 = Flip(term5); term11 = Flip(term6); term12 = Flip(term7); term13 = Flip(term8)
        return mod2([
            p4mBxy(g1, g2)*SF[0] + p4mBc2(g1, g2)*SF[1] + g1[4]*g2[4]*SF[2] + g1[5]*g2[5]*SF[3] + term4[0]*SF[4] + term5[0]*SF[5] + term6[0]*SF[6] + term7[0]*SF[7] + term8[0]*SF[8] + term9[0]*SF[9] + term10[0]*SF[10] + term11[0]*SF[11] + term12[0]*SF[12] + term13[0]*SF[13],
            p4mBxy(g1, g2)*SF[0] + p4mBc2(g1, g2)*SF[1] + g1[4]*g2[4]*SF[2] + g1[5]*g2[5]*SF[3] + term4[1]*SF[4] + term5[1]*SF[5] + term6[1]*SF[6] + term7[1]*SF[7] + term8[1]*SF[8] + term9[1]*SF[9] + term10[1]*SF[10] + term11[1]*SF[11] + term12[1]*SF[12] + term13[1]*SF[13]
        ])
    elif Action[0]==0 and Action[1]==1 and Action[2]==1 and Action[3]==0:
        term6 = p4maction2wasym1(g1, g2); term7 = p4maction2wasym2(g1, g2); term8 = Flip(term6); term9 = Flip(term7)
        return mod2([
            p4mBxy(g1, g2)*SF[0] + p4mBc2(g1, g2)*SF[1] + (g1[0]+g1[1])*(g2[0]+g2[1])*SF[2] + (g1[0]+g1[1])*g2[4]*SF[3] + g1[4]*g2[4]*SF[4] + g1[5]*g2[5]*SF[5] + term6[0]*SF[6] + term7[0]*SF[7] + term8[0]*SF[8] + term9[0]*SF[9],
            p4mBxy(g1, g2)*SF[0] + p4mBc2(g1, g2)*SF[1] + (g1[0]+g1[1])*(g2[0]+g2[1])*SF[2] + (g1[0]+g1[1])*g2[4]*SF[3] + g1[4]*g2[4]*SF[4] + g1[5]*g2[5]*SF[5] + term6[1]*SF[6] + term7[1]*SF[7] + term8[1]*SF[8] + term9[1]*SF[9]
        ])
    elif Action[0]==1 and Action[1]==0 and Action[2]==0 and Action[3]==0:
        term5 = p4maction3wasym1(g1, g2); term6 = p4maction3wasym2(g1, g2); term7 = p4maction3wasym3(g1, g2); term8 = Flip(term5); term9 = Flip(term6); term10 = Flip(term7)
        return mod2([
            p4mBc2(g1, g2)*SF[0] + g1[3]*g2[3]*SF[1] + g1[3]*g2[4]*SF[2] + g1[4]*g2[4]*SF[3] + g1[5]*g2[5]*SF[4] + term5[0]*SF[5] + term6[0]*SF[6] + term7[0]*SF[7] + term8[0]*SF[8] + term9[0]*SF[9] + term10[0]*SF[10],
            p4mBc2(g1, g2)*SF[0] + g1[3]*g2[3]*SF[1] + g1[3]*g2[4]*SF[2] + g1[4]*g2[4]*SF[3] + g1[5]*g2[5]*SF[4] + term5[1]*SF[5] + term6[1]*SF[6] + term7[1]*SF[7] + term8[1]*SF[8] + term9[1]*SF[9] + term10[1]*SF[10]
        ])
    elif Action[0]==1 and Action[1]==0 and Action[2]==1 and Action[3]==0:
        return mod2([
            p4mBxy(g1, g2)*SF[0] + p4mBc2(g1, g2)*SF[1] + g1[3]*g2[3]*SF[2] + g1[2]*g2[4]*SF[3] + g1[3]*g2[4]*SF[4] + g1[4]*g2[4]*SF[5] + g1[5]*g2[5]*SF[6],
            p4mBxy(g1, g2)*SF[0] + p4mBc2(g1, g2)*SF[1] + g1[3]*g2[3]*SF[2] + g1[2]*g2[4]*SF[3] + g1[3]*g2[4]*SF[4] + g1[4]*g2[4]*SF[5] + g1[5]*g2[5]*SF[6]
        ])
    elif Action[0]==1 and Action[1]==1 and Action[2]==0 and Action[3]==0:
        return mod2([
            p4mBxy(g1, g2)*SF[0] + p4mBc2(g1, g2)*SF[1] + g1[3]*g2[3]*SF[2] + g1[2]*g2[4]*SF[3] + g1[3]*g2[4]*SF[4] + g1[4]*g2[4]*SF[5] + g1[5]*g2[5]*SF[6],
            p4mBxy(g1, g2)*SF[0] + p4mBc2(g1, g2)*SF[1] + g1[3]*g2[3]*SF[2] + g1[2]*g2[4]*SF[3] + g1[3]*g2[4]*SF[4] + g1[4]*g2[4]*SF[5] + g1[5]*g2[5]*SF[6]
        ])
    elif Action[0]==1 and Action[1]==1 and Action[2]==1 and Action[3]==0:
        term5 = p4maction4wasym1(g1, g2); term6 = p4maction4wasym2(g1, g2); term7 = p4maction4wasym3(g1, g2); term8 = Flip(term5); term9 = Flip(term6); term10 = Flip(term7)
        return mod2([
            p4mBc2(g1, g2)*SF[0] + g1[3]*g2[3]*SF[1] + g1[3]*g2[4]*SF[2] + g1[4]*g2[4]*SF[3] + g1[5]*g2[5]*SF[4] + term5[0]*SF[5] + term6[0]*SF[6] + term7[0]*SF[7] + term8[0]*SF[8] + term9[0]*SF[9] + term10[0]*SF[10],
            p4mBc2(g1, g2)*SF[0] + g1[3]*g2[3]*SF[1] + g1[3]*g2[4]*SF[2] + g1[4]*g2[4]*SF[3] + g1[5]*g2[5]*SF[4] + term5[1]*SF[5] + term6[1]*SF[6] + term7[1]*SF[7] + term8[1]*SF[8] + term9[1]*SF[9] + term10[1]*SF[10]
        ])

def p4mO3Multiply(Action, SF):
    return [
        IndicatorZ2T([0,0,0,0,1,0], Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate),
        IndicatorZ2T([0,0,0,1,0,0], Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate),
        IndicatorZ2T([0,0,2,0,1,0], Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate),
        IndicatorZ2T([0,0,1,1,0,0], Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate),
        IndicatorZ2TZ2T([0,0,0,0,1,0], [0,0,2,0,1,0], Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate),
        IndicatorZ2TZ2T([0,0,0,0,1,0], [0,0,0,1,0,0], Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate),
        IndicatorZ2TZ2T([0,0,1,1,0,0], [0,0,0,0,1,0], Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate),
        IndicatorZ2TZ2T([0,0,2,0,1,0], [0,0,0,1,0,0], Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate),
        IndicatorZ2TZ2T([0,0,1,1,0,0], [0,0,2,0,1,0], Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate),
        IndicatorZ2T([1,0,0,1,0,0], Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate),
        IndicatorZ2T([1,0,2,0,1,0], Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate),
        IndicatorZ2T([1,1,2,0,1,0], Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate),
        IndicatorZ2TZ2T([1,0,0,1,0,0], [0,0,0,0,1,0], Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate),
        IndicatorZ2TZ2T([0,0,0,0,1,0], [1,0,2,0,1,0], Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate),
        IndicatorZ2TZ2T([0,0,0,0,1,0], [1,1,2,0,1,0], Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate),
        IndicatorZ2TZ2T([0,0,0,1,0,0], [0,1,2,0,1,0], Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate),
        IndicatorZ2TZ2T([0,0,0,1,0,0], [0,1,2,1,0,0], Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate),
        IndicatorZ2TZ2T([0,0,1,1,0,0], [1,-1,2,0,1,0], Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate),
        IndicatorZ2TZ2T([1,0,0,1,0,0], [1,1,2,0,1,0], Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate),
        IndicatorSO3(Action, SF, p4mO3SFGenerate),
        IndicatorZ2T([0,0,0,0,1,1], Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate),
        IndicatorZ2T([0,0,0,1,0,1], Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate),
        IndicatorZ2T([0,0,2,0,1,1], Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate),
        IndicatorZ2T([0,0,1,1,0,1], Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate),
        IndicatorZ2T([1,0,0,1,0,1], Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate),
        IndicatorZ2T([1,0,2,0,1,1], Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate),
        IndicatorZ2T([1,1,2,0,1,1], Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate),
        IndicatorZ2([0,0,1,1,1,0], Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate),
        IndicatorZ2([0,0,0,1,1,0], Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate),
        IndicatorZ2([1,0,0,1,1,0], Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate)
    ]

p4mO3Anomaly0 = [0]*30
p4mO3Anomalya = [0]*30; p4mO3Anomalya[2]=1; p4mO3Anomalya[4]=1
p4mO3Anomalyb = [0]*30; p4mO3Anomalyb[11]=1; p4mO3Anomalyb[14]=1
p4mO3Anomalyc = [0]*30; p4mO3Anomalyc[10]=1; p4mO3Anomalyc[13]=1
p4mO3Anomalyab = mod2(addList(p4mO3Anomalya, p4mO3Anomalyb))
p4mO3Anomalyac = mod2(addList(p4mO3Anomalya, p4mO3Anomalyc))
p4mO3Anomalybc = mod2(addList(p4mO3Anomalyb, p4mO3Anomalyc))
p4mO3Anomalyabc = mod2(addList(p4mO3Anomalya, addList(p4mO3Anomalyb, p4mO3Anomalyc)))

def get_p4m_ActionList(Action):
    if Action == 1: return [0,0,0,0]
    elif 2 <= Action <= 9: return _int_digits(Action-2, 3) + [1]
    elif 10 <= Action <= 16: return _int_digits(Action-9, 3) + [0]

def p4mO3Generate(Action, homotopylist):
    result = [[] for _ in range(len(homotopylist))]
    matchinganomaly = []
    for h in homotopylist:
        if h == "0": matchinganomaly.append(p4mO3Anomaly0)
        elif h == "a": matchinganomaly.append(p4mO3Anomalya)
        elif h == "b": matchinganomaly.append(p4mO3Anomalyb)
        elif h == "c": matchinganomaly.append(p4mO3Anomalyc)
        elif h == "a+b": matchinganomaly.append(p4mO3Anomalyab)
        elif h == "a+c": matchinganomaly.append(p4mO3Anomalyac)
        elif h == "b+c": matchinganomaly.append(p4mO3Anomalybc)
        elif h == "a+b+c": matchinganomaly.append(p4mO3Anomalyabc)
        
    ActionList = get_p4m_ActionList(Action)
    
    if Action == 1:
        for i in range(2**11):
            for j in range(i+1):
                SFCe = _int_digits(i, 11); SFCm = _int_digits(j, 11)
                Anomaly = p4mO3Multiply(ActionList, [SFCe, SFCm])
                for k in range(len(homotopylist)):
                    if Anomaly == matchinganomaly[k]:
                        result[k].append(SFCe + SFCm); break
    elif (2 <= Action <= 10) or Action in [14, 15]:
        for i in range(2**7):
            SFCe = _int_digits(i, 7)
            Anomaly = p4mO3Multiply(ActionList, SFCe)
            for k in range(len(homotopylist)):
                if Anomaly == matchinganomaly[k]:
                    result[k].append(SFCe); break
    elif Action == 11:
        for i in range(2**4):
            for j in range(2**5):
                for k_idx in range(j+1):
                    SFCe = _int_digits(i, 4) + _int_digits(j, 5) + _int_digits(k_idx, 5)
                    Anomaly = p4mO3Multiply(ActionList, SFCe)
                    for l in range(len(homotopylist)):
                        if Anomaly == matchinganomaly[l]:
                            result[l].append(SFCe); break
    elif Action == 12:
        for i in range(2**6):
            for j in range(2**2):
                for k_idx in range(j+1):
                    SFCe = _int_digits(i, 6) + _int_digits(j, 2) + _int_digits(k_idx, 2)
                    Anomaly = p4mO3Multiply(ActionList, SFCe)
                    for l in range(len(homotopylist)):
                        if Anomaly == matchinganomaly[l]:
                            result[l].append(SFCe); break
    elif Action in [13, 16]:
        for i in range(2**5):
            for j in range(2**3):
                for k_idx in range(j+1):
                    SFCe = _int_digits(i, 5) + _int_digits(j, 3) + _int_digits(k_idx, 3)
                    Anomaly = p4mO3Multiply(ActionList, SFCe)
                    for l in range(len(homotopylist)):
                        if Anomaly == matchinganomaly[l]:
                            result[l].append(SFCe); break
    return result

def p4mO3CheckSF(Action, SF):
    ActionList = get_p4m_ActionList(Action)
    if Action == 1:
        Anomaly = p4mO3Multiply(ActionList, [SF[0:11], SF[11:22]])
    else:
        Anomaly = p4mO3Multiply(ActionList, SF)
        
    if Anomaly == p4mO3Anomaly0: return "0"
    elif Anomaly == p4mO3Anomalya: return "a"
    elif Anomaly == p4mO3Anomalyb: return "b"
    elif Anomaly == p4mO3Anomalyc: return "c"
    elif Anomaly == p4mO3Anomalyab: return "a+b"
    elif Anomaly == p4mO3Anomalyac: return "a+c"
    elif Anomaly == p4mO3Anomalybc: return "b+c"
    elif Anomaly == p4mO3Anomalyabc: return "a+b+c"
    return "empty"

def p4mZ2ActionGenerate(g, Action):
    return ((g[0]+g[1])*Action[0] + g[2]*Action[1] + g[3]*Action[2] + g[4]*Action[3]) % 2

def p4mZ2SFGenerate(g1, g2, Action, SF):
    if Action[0]==0 and Action[1]==0 and Action[2]==0 and Action[3]==0:
        return mod2([
            p4mBxy(g1, g2)*SF[0][0] + p4mBc2(g1, g2)*SF[0][1] + (g1[0]+g1[1])*(g2[0]+g2[1])*SF[0][2] +
            (g1[0]+g1[1])*g2[3]*SF[0][3] + g1[2]*g2[2]*SF[0][4] + g1[3]*g2[3]*SF[0][5] +
            (g1[0]+g1[1])*g2[4]*SF[0][6] + g1[2]*g2[4]*SF[0][7] + g1[3]*g2[4]*SF[0][8] +
            g1[4]*g2[4]*SF[0][9],
            p4mBxy(g1, g2)*SF[1][0] + p4mBc2(g1, g2)*SF[1][1] + (g1[0]+g1[1])*(g2[0]+g2[1])*SF[1][2] +
            (g1[0]+g1[1])*g2[3]*SF[1][3] + g1[2]*g2[2]*SF[1][4] + g1[3]*g2[3]*SF[1][5] +
            (g1[0]+g1[1])*g2[4]*SF[1][6] + g1[2]*g2[4]*SF[1][7] + g1[3]*g2[4]*SF[1][8] +
            g1[4]*g2[4]*SF[1][9]
        ])
    elif Action[3]==1:
        return mod2([
            p4mBxy(g1, g2)*SF[0] + p4mBc2(g1, g2)*SF[1] + (g1[0]+g1[1])*(g2[0]+g2[1])*SF[2] +
            (g1[0]+g1[1])*g2[3]*SF[3] + g1[2]*g2[2]*SF[4] + g1[3]*g2[3]*SF[5],
            p4mBxy(g1, g2)*SF[0] + p4mBc2(g1, g2)*SF[1] + (g1[0]+g1[1])*(g2[0]+g2[1])*SF[2] +
            (g1[0]+g1[1])*g2[3]*SF[3] + g1[2]*g2[2]*SF[4] + g1[3]*g2[3]*SF[5]
        ])
    elif Action[0]==0 and Action[1]==0 and Action[2]==1 and Action[3]==0:
        return mod2([
            p4mBxy(g1, g2)*SF[0] + p4mBc2(g1, g2)*SF[1] + (g1[0]+g1[1])*(g2[0]+g2[1])*SF[2] +
            (g1[0]+g1[1])*g2[4]*SF[3] + g1[2]*g2[4]*SF[4] + g1[4]*g2[4]*SF[5],
            p4mBxy(g1, g2)*SF[0] + p4mBc2(g1, g2)*SF[1] + (g1[0]+g1[1])*(g2[0]+g2[1])*SF[2] +
            (g1[0]+g1[1])*g2[4]*SF[3] + g1[2]*g2[4]*SF[4] + g1[4]*g2[4]*SF[5]
        ])
    elif Action[0]==0 and Action[1]==1 and Action[2]==0 and Action[3]==0:
        term4 = p4maction1wasym1(g1, g2); term5 = p4maction1wasym2(g1, g2); term6 = p4maction1wasym3(g1, g2); term7 = p4maction1wasym4(g1, g2); term8 = p4maction1wasym5(g1, g2)
        term9 = Flip(term4); term10 = Flip(term5); term11 = Flip(term6); term12 = Flip(term7); term13 = Flip(term8)
        return mod2([
            p4mBxy(g1, g2)*SF[0] + p4mBc2(g1, g2)*SF[1] + g1[4]*g2[4]*SF[2] + term4[0]*SF[3] + term5[0]*SF[4] + term6[0]*SF[5] + term7[0]*SF[6] + term8[0]*SF[7] + term9[0]*SF[8] + term10[0]*SF[9] + term11[0]*SF[10] + term12[0]*SF[11] + term13[0]*SF[12],
            p4mBxy(g1, g2)*SF[0] + p4mBc2(g1, g2)*SF[1] + g1[4]*g2[4]*SF[2] + term4[1]*SF[3] + term5[1]*SF[4] + term6[1]*SF[5] + term7[1]*SF[6] + term8[1]*SF[7] + term9[1]*SF[8] + term10[1]*SF[9] + term11[1]*SF[10] + term12[1]*SF[11] + term13[1]*SF[12]
        ])
    elif Action[0]==0 and Action[1]==1 and Action[2]==1 and Action[3]==0:
        term6 = p4maction2wasym1(g1, g2); term7 = p4maction2wasym2(g1, g2); term8 = Flip(term6); term9 = Flip(term7)
        return mod2([
            p4mBxy(g1, g2)*SF[0] + p4mBc2(g1, g2)*SF[1] + (g1[0]+g1[1])*(g2[0]+g2[1])*SF[2] + (g1[0]+g1[1])*g2[4]*SF[3] + g1[4]*g2[4]*SF[4] + term6[0]*SF[5] + term7[0]*SF[6] + term8[0]*SF[7] + term9[0]*SF[8],
            p4mBxy(g1, g2)*SF[0] + p4mBc2(g1, g2)*SF[1] + (g1[0]+g1[1])*(g2[0]+g2[1])*SF[2] + (g1[0]+g1[1])*g2[4]*SF[3] + g1[4]*g2[4]*SF[4] + term6[1]*SF[5] + term7[1]*SF[6] + term8[1]*SF[7] + term9[1]*SF[8]
        ])
    elif Action[0]==1 and Action[1]==0 and Action[2]==0 and Action[3]==0:
        term5 = p4maction3wasym1(g1, g2); term6 = p4maction3wasym2(g1, g2); term7 = p4maction3wasym3(g1, g2); term8 = Flip(term5); term9 = Flip(term6); term10 = Flip(term7)
        return mod2([
            p4mBc2(g1, g2)*SF[0] + g1[3]*g2[3]*SF[1] + g1[3]*g2[4]*SF[2] + g1[4]*g2[4]*SF[3] + term5[0]*SF[4] + term6[0]*SF[5] + term7[0]*SF[6] + term8[0]*SF[7] + term9[0]*SF[8] + term10[0]*SF[9],
            p4mBc2(g1, g2)*SF[0] + g1[3]*g2[3]*SF[1] + g1[3]*g2[4]*SF[2] + g1[4]*g2[4]*SF[3] + term5[1]*SF[4] + term6[1]*SF[5] + term7[1]*SF[6] + term8[1]*SF[7] + term9[1]*SF[8] + term10[1]*SF[9]
        ])
    elif Action[0]==1 and Action[1]==0 and Action[2]==1 and Action[3]==0:
        return mod2([
            p4mBxy(g1, g2)*SF[0] + p4mBc2(g1, g2)*SF[1] + g1[3]*g2[3]*SF[2] + g1[2]*g2[4]*SF[3] + g1[3]*g2[4]*SF[4] + g1[4]*g2[4]*SF[5],
            p4mBxy(g1, g2)*SF[0] + p4mBc2(g1, g2)*SF[1] + g1[3]*g2[3]*SF[2] + g1[2]*g2[4]*SF[3] + g1[3]*g2[4]*SF[4] + g1[4]*g2[4]*SF[5]
        ])
    elif Action[0]==1 and Action[1]==1 and Action[2]==0 and Action[3]==0:
        return mod2([
            p4mBxy(g1, g2)*SF[0] + p4mBc2(g1, g2)*SF[1] + g1[3]*g2[3]*SF[2] + g1[2]*g2[4]*SF[3] + g1[3]*g2[4]*SF[4] + g1[4]*g2[4]*SF[5],
            p4mBxy(g1, g2)*SF[0] + p4mBc2(g1, g2)*SF[1] + g1[3]*g2[3]*SF[2] + g1[2]*g2[4]*SF[3] + g1[3]*g2[4]*SF[4] + g1[4]*g2[4]*SF[5]
        ])
    elif Action[0]==1 and Action[1]==1 and Action[2]==1 and Action[3]==0:
        term5 = p4maction4wasym1(g1, g2); term6 = p4maction4wasym2(g1, g2); term7 = p4maction4wasym3(g1, g2); term8 = Flip(term5); term9 = Flip(term6); term10 = Flip(term7)
        return mod2([
            p4mBc2(g1, g2)*SF[0] + g1[3]*g2[3]*SF[1] + g1[3]*g2[4]*SF[2] + g1[4]*g2[4]*SF[3] + term5[0]*SF[4] + term6[0]*SF[5] + term7[0]*SF[6] + term8[0]*SF[7] + term9[0]*SF[8] + term10[0]*SF[9],
            p4mBc2(g1, g2)*SF[0] + g1[3]*g2[3]*SF[1] + g1[3]*g2[4]*SF[2] + g1[4]*g2[4]*SF[3] + term5[1]*SF[4] + term6[1]*SF[5] + term7[1]*SF[6] + term8[1]*SF[7] + term9[1]*SF[8] + term10[1]*SF[9]
        ])

def p4mZ2Multiply(Action, SF):
    return [
        IndicatorZ2T([0,0,0,0,1], Action, SF, p4mZ2ActionGenerate, p4mZ2SFGenerate),
        IndicatorZ2T([0,0,0,1,0], Action, SF, p4mZ2ActionGenerate, p4mZ2SFGenerate),
        IndicatorZ2T([0,0,2,0,1], Action, SF, p4mZ2ActionGenerate, p4mZ2SFGenerate),
        IndicatorZ2T([0,0,1,1,0], Action, SF, p4mZ2ActionGenerate, p4mZ2SFGenerate),
        IndicatorZ2TZ2T([0,0,0,0,1], [0,0,2,0,1], Action, SF, p4mZ2ActionGenerate, p4mZ2SFGenerate),
        IndicatorZ2TZ2T([0,0,0,0,1], [0,0,0,1,0], Action, SF, p4mZ2ActionGenerate, p4mZ2SFGenerate),
        IndicatorZ2TZ2T([0,0,1,1,0], [0,0,0,0,1], Action, SF, p4mZ2ActionGenerate, p4mZ2SFGenerate),
        IndicatorZ2TZ2T([0,0,2,0,1], [0,0,0,1,0], Action, SF, p4mZ2ActionGenerate, p4mZ2SFGenerate),
        IndicatorZ2TZ2T([0,0,1,1,0], [0,0,2,0,1], Action, SF, p4mZ2ActionGenerate, p4mZ2SFGenerate),
        IndicatorZ2T([1,0,0,1,0], Action, SF, p4mZ2ActionGenerate, p4mZ2SFGenerate),
        IndicatorZ2T([1,0,2,0,1], Action, SF, p4mZ2ActionGenerate, p4mZ2SFGenerate),
        IndicatorZ2T([1,1,2,0,1], Action, SF, p4mZ2ActionGenerate, p4mZ2SFGenerate),
        IndicatorZ2TZ2T([1,0,0,1,0], [0,0,0,0,1], Action, SF, p4mZ2ActionGenerate, p4mZ2SFGenerate),
        IndicatorZ2TZ2T([0,0,0,0,1], [1,0,2,0,1], Action, SF, p4mZ2ActionGenerate, p4mZ2SFGenerate),
        IndicatorZ2TZ2T([0,0,0,0,1], [1,1,2,0,1], Action, SF, p4mZ2ActionGenerate, p4mZ2SFGenerate),
        IndicatorZ2TZ2T([0,0,0,1,0], [0,1,2,0,1], Action, SF, p4mZ2ActionGenerate, p4mZ2SFGenerate),
        IndicatorZ2TZ2T([0,0,0,1,0], [0,1,2,1,0], Action, SF, p4mZ2ActionGenerate, p4mZ2SFGenerate),
        IndicatorZ2TZ2T([0,0,1,1,0], [1,-1,2,0,1], Action, SF, p4mZ2ActionGenerate, p4mZ2SFGenerate),
        IndicatorZ2TZ2T([1,0,0,1,0], [1,1,2,0,1], Action, SF, p4mZ2ActionGenerate, p4mZ2SFGenerate)
    ]

p4mZ2Anomaly0 = [0]*19
p4mZ2Anomalya = [0]*19; p4mZ2Anomalya[2]=1; p4mZ2Anomalya[4]=1
p4mZ2Anomalyb = [0]*19; p4mZ2Anomalyb[11]=1; p4mZ2Anomalyb[14]=1
p4mZ2Anomalyc = [0]*19; p4mZ2Anomalyc[10]=1; p4mZ2Anomalyc[13]=1
p4mZ2Anomalyab = mod2(addList(p4mZ2Anomalya, p4mZ2Anomalyb))
p4mZ2Anomalyac = mod2(addList(p4mZ2Anomalya, p4mZ2Anomalyc))
p4mZ2Anomalybc = mod2(addList(p4mZ2Anomalyb, p4mZ2Anomalyc))
p4mZ2Anomalyabc = mod2(addList(p4mZ2Anomalya, addList(p4mZ2Anomalyb, p4mZ2Anomalyc)))

def p4mZ2Generate(Action, homotopylist):
    result = [[] for _ in range(len(homotopylist))]
    matchinganomaly = []
    for h in homotopylist:
        if h == "0": matchinganomaly.append(p4mZ2Anomaly0)
        elif h == "a": matchinganomaly.append(p4mZ2Anomalya)
        elif h == "b": matchinganomaly.append(p4mZ2Anomalyb)
        elif h == "c": matchinganomaly.append(p4mZ2Anomalyc)
        elif h == "a+b": matchinganomaly.append(p4mZ2Anomalyab)
        elif h == "a+c": matchinganomaly.append(p4mZ2Anomalyac)
        elif h == "b+c": matchinganomaly.append(p4mZ2Anomalybc)
        elif h == "a+b+c": matchinganomaly.append(p4mZ2Anomalyabc)
        
    ActionList = get_p4m_ActionList(Action)
    
    if Action == 1:
        for i in range(2**10):
            for j in range(i+1):
                SFCe = _int_digits(i, 10); SFCm = _int_digits(j, 10)
                Anomaly = p4mZ2Multiply(ActionList, [SFCe, SFCm])
                for k in range(len(homotopylist)):
                    if Anomaly == matchinganomaly[k]:
                        result[k].append(SFCe + SFCm); break
    elif (2 <= Action <= 10) or Action in [14, 15]:
        for i in range(2**6):
            SFCe = _int_digits(i, 6)
            Anomaly = p4mZ2Multiply(ActionList, SFCe)
            for k in range(len(homotopylist)):
                if Anomaly == matchinganomaly[k]:
                    result[k].append(SFCe); break
    elif Action == 11:
        for i in range(2**3):
            for j in range(2**5):
                for k_idx in range(j+1):
                    SFCe = _int_digits(i, 3) + _int_digits(j, 5) + _int_digits(k_idx, 5)
                    Anomaly = p4mZ2Multiply(ActionList, SFCe)
                    for l in range(len(homotopylist)):
                        if Anomaly == matchinganomaly[l]:
                            result[l].append(SFCe); break
    elif Action == 12:
        for i in range(2**5):
            for j in range(2**2):
                for k_idx in range(j+1):
                    SFCe = _int_digits(i, 5) + _int_digits(j, 2) + _int_digits(k_idx, 2)
                    Anomaly = p4mZ2Multiply(ActionList, SFCe)
                    for l in range(len(homotopylist)):
                        if Anomaly == matchinganomaly[l]:
                            result[l].append(SFCe); break
    elif Action in [13, 16]:
        for i in range(2**4):
            for j in range(2**3):
                for k_idx in range(j+1):
                    SFCe = _int_digits(i, 4) + _int_digits(j, 3) + _int_digits(k_idx, 3)
                    Anomaly = p4mZ2Multiply(ActionList, SFCe)
                    for l in range(len(homotopylist)):
                        if Anomaly == matchinganomaly[l]:
                            result[l].append(SFCe); break
    return result

def p4mZ2CheckSF(Action, SF):
    ActionList = get_p4m_ActionList(Action)
    if Action == 1:
        Anomaly = p4mZ2Multiply(ActionList, [SF[0:10], SF[10:20]])
    else:
        Anomaly = p4mZ2Multiply(ActionList, SF)
        
    if Anomaly == p4mZ2Anomaly0: return "0"
    elif Anomaly == p4mZ2Anomalya: return "a"
    elif Anomaly == p4mZ2Anomalyb: return "b"
    elif Anomaly == p4mZ2Anomalyc: return "c"
    elif Anomaly == p4mZ2Anomalyab: return "a+b"
    elif Anomaly == p4mZ2Anomalyac: return "a+c"
    elif Anomaly == p4mZ2Anomalybc: return "b+c"
    elif Anomaly == p4mZ2Anomalyabc: return "a+b+c"
    return "empty"
