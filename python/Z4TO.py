def mod2(x):
    if isinstance(x, list):
        return [item % 2 for item in x]
    return x % 2

def p6mO3Multiply(g1, g2):
    return mod2([
        g1[0]*g2[0] + g1[0]*g2[1] + g1[0]*g2[4] + g1[1]*g2[0] + g1[4]*g2[0],
        g1[0]*g2[0] + g1[0]*g2[2] + g1[2]*g2[0],
        g1[0]*g2[3] + g1[0]*g2[5] + g1[3]*g2[0] + g1[5]*g2[0],
        g1[1]*g2[1] + g1[1]*g2[4] + g1[4]*g2[1],
        g1[1]*g2[2] + g1[1]*g2[4] + g1[2]*g2[1] + g1[4]*g2[1],
        g1[1]*g2[3] + g1[2]*g2[2] + g1[2]*g2[5] + g1[3]*g2[1] + g1[3]*g2[4] + g1[4]*g2[3] + g1[5]*g2[2],
        g1[2]*g2[3] + g1[2]*g2[5] + g1[3]*g2[2] + g1[3]*g2[4] + g1[4]*g2[3] + g1[5]*g2[2],
        g1[3]*g2[3],
        g1[0]*g2[6] + g1[6]*g2[0],
        g1[1]*g2[6] + g1[4]*g2[4] + g1[4]*g2[6] + g1[6]*g2[1] + g1[6]*g2[4],
        g1[2]*g2[6] + g1[4]*g2[5] + g1[4]*g2[6] + g1[5]*g2[4] + g1[6]*g2[2] + g1[6]*g2[4],
        g1[3]*g2[6] + g1[5]*g2[5] + g1[6]*g2[3],
        g1[0]*g2[7] + g1[7]*g2[0],
        g1[1]*g2[7] + g1[4]*g2[7] + g1[7]*g2[1] + g1[7]*g2[4],
        g1[2]*g2[7] + g1[4]*g2[7] + g1[7]*g2[2] + g1[7]*g2[4],
        g1[3]*g2[7] + g1[7]*g2[3],
        g1[4]*g2[7] + g1[7]*g2[4],
        g1[5]*g2[7] + g1[7]*g2[5],
        g1[6]*g2[6],
        g1[6]*g2[7] + g1[7]*g2[6],
        g1[7]*g2[7]
    ])

def p6mO3Multiply1(g1, g2):
    return mod2([x + y for x, y in zip(
        p6mO3Multiply([g1[0], 0, g1[2], 0, g1[4], g1[5], 0, g1[7]], [0, g2[4], g2[4], 0, g2[4], g2[5], 0, 0]),
        p6mO3Multiply([0, g1[1], 0, g1[3], 0, 0, g1[6], 0], [g2[0], g2[1], g2[2], g2[3], 0, 0, g2[6], g2[7]])
    )])

def p6mO3Multiply2(g1, g2):
    return mod2([x + y for x, y in zip(
        p6mO3Multiply([0, 0, g1[2], g1[3], g1[4], g1[5], 0, g1[7]], [0, g2[4], 0, g2[5], g2[4], g2[5], 0, 0]),
        p6mO3Multiply([g1[0], g1[1], g1[1], 0, 0, g1[6], g1[6], 0], [g2[0], g2[1], g2[2], g2[3], 0, 0, g2[6], g2[7]])
    )])

def p6mO3Multiply3(g1, g2):
    return mod2([x + y for x, y in zip(
        p6mO3Multiply([g1[0], g1[1], g1[2], 0, g1[4], g1[5], 0, g1[7]], [0, 0, g2[4]+g2[5], 0, g2[4], g2[5], 0, 0]),
        p6mO3Multiply([0, 0, g1[3], g1[3], g1[6], 0, g1[6], 0], [g2[0], g2[1], g2[2], g2[3], 0, 0, g2[6], g2[7]])
    )])

def p6mO3Multiply4(g1, g2):
    return mod2([x + y for x, y in zip(
        p6mO3Multiply([g1[0], g1[1], 0, g1[3], g1[4], g1[5], 0, g1[7]], [0, 0, g2[5], g2[5], g2[4], g2[5], 0, 0]),
        p6mO3Multiply([0, 0, g1[2], 0, g1[6], g1[6], g1[6], 0], [g2[0], g2[1], g2[2], g2[3], 0, 0, g2[6], g2[7]])
    )])

p6mO3Anomaly0 = [0]*21
p6mO3Anomalya = [0]*21
p6mO3Anomalya[8] = 1; p6mO3Anomalya[9] = 1; p6mO3Anomalya[10] = 1
p6mO3Anomalya[12] = 1; p6mO3Anomalya[13] = 1; p6mO3Anomalya[14] = 1
p6mO3Anomalyc = [0]*21
p6mO3Anomalyc[8] = 1; p6mO3Anomalyc[12] = 1
p6mO3Anomalyac = mod2([x + y for x, y in zip(p6mO3Anomalya, p6mO3Anomalyc)])

def _int_digits(val, pad):
    return [int(x) for x in bin(val)[2:].zfill(pad)]

def p6mO3AnomalyCheck(multiply_func, homotopylist):
    result = [[] for _ in range(len(homotopylist))]
    matchinganomaly = []
    
    for h in homotopylist:
        if h == "0": matchinganomaly.append(p6mO3Anomaly0)
        elif h == "a": matchinganomaly.append(p6mO3Anomalya)
        elif h == "c": matchinganomaly.append(p6mO3Anomalyc)
        elif h == "a+c": matchinganomaly.append(p6mO3Anomalyac)
        
    for i in range(2**8):
        for j in range(2**8):
            SFCe = _int_digits(i, 8)
            SFCm = _int_digits(j, 8)
            Anomaly = multiply_func(SFCe, SFCm)
            
            for k in range(len(homotopylist)):
                if Anomaly == matchinganomaly[k]:
                    result[k].append([SFCe, SFCm])
                    break
    return result

def p6mO3Generate(Action, homotopylist):
    if Action == 1:
        result = p6mO3AnomalyCheck(p6mO3Multiply1, homotopylist)
    elif Action == 2:
        result = p6mO3AnomalyCheck(p6mO3Multiply2, homotopylist)
        for i in range(len(homotopylist)):
            addList = []
            for j in range(len(result[i])):
                if result[i][j][0][0] == 0:
                    add = [[x for x in result[i][j][0]], [x for x in result[i][j][1]]]
                    add[0][0] = 2
                    addList.append(add)
            result[i] = result[i] + addList
    elif Action == 3:
        result = p6mO3AnomalyCheck(p6mO3Multiply3, homotopylist)
    elif Action == 4:
        result = p6mO3AnomalyCheck(p6mO3Multiply4, homotopylist)
    return result

def p6mO3CheckSF(Action, SFCe, SFCm):
    if Action == 1: Anomaly = p6mO3Multiply1(SFCe, SFCm)
    elif Action == 2: Anomaly = p6mO3Multiply2(SFCe, SFCm)
    elif Action == 3: Anomaly = p6mO3Multiply3(SFCe, SFCm)
    elif Action == 4: Anomaly = p6mO3Multiply4(SFCe, SFCm)
    
    if Anomaly == p6mO3Anomaly0: return "0"
    elif Anomaly == p6mO3Anomalya: return "a"
    elif Anomaly == p6mO3Anomalyc: return "c"
    elif Anomaly == p6mO3Anomalyac: return "a+c"
    return "empty"


def p6mZ2Multiply(g1, g2):
    return mod2([
        g1[0]*g2[0] + g1[0]*g2[1] + g1[0]*g2[4] + g1[1]*g2[0] + g1[4]*g2[0],
        g1[0]*g2[0] + g1[0]*g2[2] + g1[2]*g2[0],
        g1[0]*g2[3] + g1[0]*g2[5] + g1[3]*g2[0] + g1[5]*g2[0],
        g1[1]*g2[1] + g1[1]*g2[4] + g1[4]*g2[1],
        g1[1]*g2[2] + g1[1]*g2[4] + g1[2]*g2[1] + g1[4]*g2[1],
        g1[1]*g2[3] + g1[2]*g2[2] + g1[2]*g2[5] + g1[3]*g2[1] + g1[3]*g2[4] + g1[4]*g2[3] + g1[5]*g2[2],
        g1[2]*g2[3] + g1[2]*g2[5] + g1[3]*g2[2] + g1[3]*g2[4] + g1[4]*g2[3] + g1[5]*g2[2],
        g1[3]*g2[3],
        g1[0]*g2[6] + g1[6]*g2[0],
        g1[1]*g2[6] + g1[4]*g2[4] + g1[4]*g2[6] + g1[6]*g2[1] + g1[6]*g2[4],
        g1[2]*g2[6] + g1[4]*g2[5] + g1[4]*g2[6] + g1[5]*g2[4] + g1[6]*g2[2] + g1[6]*g2[4],
        g1[3]*g2[6] + g1[5]*g2[5] + g1[6]*g2[3],
        g1[6]*g2[6]
    ])

def p6mZ2Multiply1(g1, g2):
    return mod2([x + y for x, y in zip(
        p6mZ2Multiply([g1[0], 0, g1[2], 0, g1[4], g1[5], 0], [0, g2[4], g2[4], 0, g2[4], g2[5], 0]),
        p6mZ2Multiply([0, g1[1], 0, g1[3], 0, 0, g1[6]], [g2[0], g2[1], g2[2], g2[3], 0, 0, g2[6]])
    )])

def p6mZ2Multiply2(g1, g2):
    return mod2([x + y for x, y in zip(
        p6mZ2Multiply([0, 0, g1[2], g1[3], g1[4], g1[5], 0], [0, g2[4], 0, g2[5], g2[4], g2[5], 0]),
        p6mZ2Multiply([g1[0], g1[1], g1[1], 0, 0, g1[6], g1[6]], [g2[0], g2[1], g2[2], g2[3], 0, 0, g2[6]])
    )])

def p6mZ2Multiply3(g1, g2):
    return mod2([x + y for x, y in zip(
        p6mZ2Multiply([g1[0], g1[1], g1[2], 0, g1[4], g1[5], 0], [0, 0, g2[4]+g2[5], 0, g2[4], g2[5], 0]),
        p6mZ2Multiply([0, 0, g1[3], g1[3], g1[6], 0, g1[6]], [g2[0], g2[1], g2[2], g2[3], 0, 0, g2[6]])
    )])

def p6mZ2Multiply4(g1, g2):
    return mod2([x + y for x, y in zip(
        p6mZ2Multiply([g1[0], g1[1], 0, g1[3], g1[4], g1[5], 0], [0, 0, g2[5], g2[5], g2[4], g2[5], 0]),
        p6mZ2Multiply([0, 0, g1[2], 0, g1[6], g1[6], g1[6]], [g2[0], g2[1], g2[2], g2[3], 0, 0, g2[6]])
    )])

p6mZ2Anomaly0 = [0]*13
p6mZ2Anomalya = [0]*13
p6mZ2Anomalya[8] = 1; p6mZ2Anomalya[9] = 1; p6mZ2Anomalya[10] = 1
p6mZ2Anomalyc = [0]*13
p6mZ2Anomalyc[8] = 1
p6mZ2Anomalyac = mod2([x + y for x, y in zip(p6mZ2Anomalya, p6mZ2Anomalyc)])

def p6mZ2AnomalyCheck(multiply_func, homotopylist):
    result = [[] for _ in range(len(homotopylist))]
    matchinganomaly = []
    
    for h in homotopylist:
        if h == "0": matchinganomaly.append(p6mZ2Anomaly0)
        elif h == "a": matchinganomaly.append(p6mZ2Anomalya)
        elif h == "c": matchinganomaly.append(p6mZ2Anomalyc)
        elif h == "a+c": matchinganomaly.append(p6mZ2Anomalyac)
        
    for i in range(2**7):
        for j in range(2**7):
            SFCe = _int_digits(i, 7)
            SFCm = _int_digits(j, 7)
            Anomaly = multiply_func(SFCe, SFCm)
            
            for k in range(len(homotopylist)):
                if Anomaly == matchinganomaly[k]:
                    result[k].append([SFCe, SFCm])
                    break
    return result

def p6mZ2Generate(Action, homotopylist):
    if Action == 1:
        result = p6mZ2AnomalyCheck(p6mZ2Multiply1, homotopylist)
    elif Action == 2:
        result = p6mZ2AnomalyCheck(p6mZ2Multiply2, homotopylist)
        for i in range(len(homotopylist)):
            addList = []
            for j in range(len(result[i])):
                if result[i][j][0][0] == 0:
                    add = [[x for x in result[i][j][0]], [x for x in result[i][j][1]]]
                    add[0][0] = 2
                    addList.append(add)
            result[i] = result[i] + addList
    elif Action == 3:
        result = p6mZ2AnomalyCheck(p6mZ2Multiply3, homotopylist)
    elif Action == 4:
        result = p6mZ2AnomalyCheck(p6mZ2Multiply4, homotopylist)
    return result

def p6mZ2CheckSF(Action, SFCe, SFCm):
    if Action == 1: Anomaly = p6mZ2Multiply1(SFCe, SFCm)
    elif Action == 2: Anomaly = p6mZ2Multiply2(SFCe, SFCm)
    elif Action == 3: Anomaly = p6mZ2Multiply3(SFCe, SFCm)
    elif Action == 4: Anomaly = p6mZ2Multiply4(SFCe, SFCm)
    
    if Anomaly == p6mZ2Anomaly0: return "0"
    elif Anomaly == p6mZ2Anomalya: return "a"
    elif Anomaly == p6mZ2Anomalyc: return "c"
    elif Anomaly == p6mZ2Anomalyac: return "a+c"
    return "empty"


def p4mO3Multiply(g1, g2):
    return mod2([
        g1[0]*g2[0] + g1[0]*g2[1] + g1[1]*g2[0],
        g1[0]*g2[2] + g1[0]*g2[3] + g1[0]*g2[4] + g1[0]*g2[6] + g1[0]*g2[7] + g1[1]*g2[2] + g1[1]*g2[3] + g1[1]*g2[6] + g1[2]*g2[0] + g1[2]*g2[1] + g1[3]*g2[0] + g1[3]*g2[1] + g1[4]*g2[0] + g1[6]*g2[0] + g1[6]*g2[1] + g1[7]*g2[0],
        g1[0]*g2[2] + g1[0]*g2[3] + g1[0]*g2[5] + g1[0]*g2[6] + g1[0]*g2[8] + g1[1]*g2[2] + g1[1]*g2[3] + g1[1]*g2[6] + g1[2]*g2[0] + g1[2]*g2[1] + g1[3]*g2[0] + g1[3]*g2[1] + g1[5]*g2[0] + g1[6]*g2[0] + g1[6]*g2[1] + g1[8]*g2[0],
        g1[1]*g2[1],
        g1[1]*g2[4] + g1[1]*g2[7] + g1[4]*g2[1] + g1[7]*g2[1],
        g1[1]*g2[5] + g1[1]*g2[8] + g1[5]*g2[1] + g1[8]*g2[1],
        g1[1]*g2[2] + g1[1]*g2[6] + g1[2]*g2[1] + g1[2]*g2[2] + g1[2]*g2[6] + g1[6]*g2[1] + g1[6]*g2[2],
        g1[1]*g2[2] + g1[1]*g2[3] + g1[1]*g2[6] + g1[2]*g2[1] + g1[2]*g2[3] + g1[2]*g2[6] + g1[3]*g2[1] + g1[3]*g2[2] + g1[6]*g2[1] + g1[6]*g2[2],
        g1[1]*g2[3] + g1[2]*g2[5] + g1[3]*g2[1] + g1[3]*g2[3] + g1[3]*g2[8] + g1[5]*g2[2] + g1[5]*g2[6] + g1[6]*g2[5] + g1[8]*g2[3],
        g1[3]*g2[5] + g1[3]*g2[8] + g1[5]*g2[3] + g1[5]*g2[6] + g1[6]*g2[5] + g1[8]*g2[3],
        g1[4]*g2[4] + g1[4]*g2[5] + g1[5]*g2[4],
        g1[5]*g2[5],
        g1[0]*g2[9] + g1[9]*g2[0],
        g1[1]*g2[9] + g1[9]*g2[1],
        g1[2]*g2[9] + g1[6]*g2[6] + g1[6]*g2[9] + g1[9]*g2[2] + g1[9]*g2[6],
        g1[3]*g2[9] + g1[6]*g2[8] + g1[6]*g2[9] + g1[8]*g2[6] + g1[9]*g2[3] + g1[9]*g2[6],
        g1[4]*g2[9] + g1[7]*g2[7] + g1[7]*g2[8] + g1[8]*g2[7] + g1[9]*g2[4],
        g1[5]*g2[9] + g1[8]*g2[8] + g1[9]*g2[5],
        g1[0]*g2[10] + g1[10]*g2[0],
        g1[1]*g2[10] + g1[10]*g2[1],
        g1[2]*g2[10] + g1[6]*g2[10] + g1[10]*g2[2] + g1[10]*g2[6],
        g1[3]*g2[10] + g1[6]*g2[10] + g1[10]*g2[3] + g1[10]*g2[6],
        g1[4]*g2[10] + g1[10]*g2[4],
        g1[5]*g2[10] + g1[10]*g2[5],
        g1[6]*g2[10] + g1[10]*g2[6],
        g1[7]*g2[10] + g1[10]*g2[7],
        g1[8]*g2[10] + g1[10]*g2[8],
        g1[9]*g2[9],
        g1[9]*g2[10] + g1[10]*g2[9],
        g1[10]*g2[10]
    ])

def p4mO3Multiply1(g1, g2):
    return mod2([x + y for x, y in zip(
        p4mO3Multiply([g1[0], g1[1], 0, g1[3], 0, 0, g1[6], g1[7], g1[8], 0, g1[10]], [0, 0, g2[6], g2[6], 0, 0, g2[6], g2[7], g2[8], 0, 0]),
        p4mO3Multiply([0, 0, g1[2], 0, g1[4], g1[5], 0, 0, 0, g1[9], 0], [g2[0], g2[1], g2[2], g2[3], g2[4], g2[5], 0, 0, 0, g2[9], g2[10]])
    )])

def p4mO3Multiply2(g1, g2):
    return mod2([x + y for x, y in zip(
        p4mO3Multiply([0, 0, 0, g1[3], g1[4], g1[5], g1[6], g1[7], g1[8], 0, g1[10]], [0, 0, g2[6], 0, g2[7], g2[8], g2[6], g2[7], g2[8], 0, 0]),
        p4mO3Multiply([g1[0], g1[1], g1[2], g1[2], 0, 0, 0, 0, g1[9], g1[9], 0], [g2[0], g2[1], g2[2], g2[3], g2[4], g2[5], 0, 0, 0, g2[9], g2[10]])
    )])

def p4mO3Multiply3(g1, g2):
    return mod2([x + y for x, y in zip(
        p4mO3Multiply([g1[0], g1[1], 0, g1[3], 0, g1[5], g1[6], g1[7], g1[8], 0, g1[10]], [0, 0, g2[6], g2[6], g2[7]+g2[8], 0, g2[6], g2[7], g2[8], 0, 0]),
        p4mO3Multiply([0, 0, g1[2], 0, g1[4], g1[4], 0, g1[9], 0, g1[9], 0], [g2[0], g2[1], g2[2], g2[3], g2[4], g2[5], 0, 0, 0, g2[9], g2[10]])
    )])

def p4mO3Multiply4(g1, g2):
    return mod2([x + y for x, y in zip(
        p4mO3Multiply([g1[0], g1[1], 0, g1[3], 0, g1[5], g1[6], g1[7], g1[8], 0, g1[10]], [0, 0, g2[6], 0, g2[8], g2[8], g2[6], g2[7], g2[8], 0, 0]),
        p4mO3Multiply([0, 0, g1[2], g1[2], g1[4], 0, 0, g1[9], g1[9], g1[9], 0], [g2[0], g2[1], g2[2], g2[3], g2[4], g2[5], 0, 0, 0, g2[9], g2[10]])
    )])

def p4mO3Multiply5(g1, g2):
    return mod2([x + y for x, y in zip(
        p4mO3Multiply([g1[0], g1[1], g1[2], g1[3], 0, 0, g1[6], g1[7], g1[8], 0, g1[10]], [0, 0, 0, g2[6]+g2[8], 0, 0, g2[6], g2[7], g2[8], 0, 0]),
        p4mO3Multiply([0, 0, 0, g1[5], g1[4], g1[5], g1[9], 0, 0, g1[9], 0], [g2[0], g2[1], g2[2], g2[3], g2[4], g2[5], 0, 0, 0, g2[9], g2[10]])
    )])

def p4mO3Multiply6(g1, g2):
    return mod2([x + y for x, y in zip(
        p4mO3Multiply([0, g1[1], g1[2], 0, g1[4], g1[5], g1[6], g1[7], g1[8], 0, g1[10]], [0, 0, 0, g2[8], g2[7], g2[8], g2[6], g2[7], g2[8], 0, 0]),
        p4mO3Multiply([g1[0], g1[0], g1[0], g1[0]+g1[3], 0, 0, g1[9], 0, g1[9], g1[9], 0], [g2[0], g2[1], g2[2], g2[3], g2[4], g2[5], 0, 0, 0, g2[9], g2[10]])
    )])

def p4mO3Multiply7(g1, g2):
    return mod2([x + y for x, y in zip(
        p4mO3Multiply([0, g1[1], g1[2], g1[3], g1[4], 0, g1[6], g1[7], g1[8], 0, g1[10]], [0, 0, 0, g2[6]+g2[8], g2[7]+g2[8], 0, g2[6], g2[7], g2[8], 0, 0]),
        p4mO3Multiply([g1[0], 0, 0, g1[5], g1[5], g1[5], g1[9], g1[9], 0, g1[9], 0], [g2[0], g2[1], g2[2], g2[3], g2[4], g2[5], 0, 0, 0, g2[9], g2[10]])
    )])

def p4mO3Multiply8(g1, g2):
    return mod2([x + y for x, y in zip(
        p4mO3Multiply([g1[0], g1[1], g1[2], 0, 0, g1[5], g1[6], g1[7], g1[8], 0, g1[10]], [0, 0, 0, g2[8], g2[8], g2[8], g2[6], g2[7], g2[8], 0, 0]),
        p4mO3Multiply([0, 0, 0, g1[3], g1[3]+g1[4], 0, g1[9], g1[9], g1[9], g1[9], 0], [g2[0], g2[1], g2[2], g2[3], g2[4], g2[5], 0, 0, 0, g2[9], g2[10]])
    )])

p4mO3Anomaly0 = [0]*30
p4mO3Anomalya = [0]*30
p4mO3Anomalya[12] = 1; p4mO3Anomalya[13] = 1; p4mO3Anomalya[14] = 1; p4mO3Anomalya[15] = 1
p4mO3Anomalya[18] = 1; p4mO3Anomalya[19] = 1; p4mO3Anomalya[20] = 1; p4mO3Anomalya[21] = 1
p4mO3Anomalyb = [0]*30
p4mO3Anomalyb[12] = 1; p4mO3Anomalyb[18] = 1
p4mO3Anomalyc = [0]*30
p4mO3Anomalyc[14] = 1; p4mO3Anomalyc[15] = 1; p4mO3Anomalyc[20] = 1; p4mO3Anomalyc[21] = 1

p4mO3Anomalyab = mod2([x + y for x, y in zip(p4mO3Anomalya, p4mO3Anomalyb)])
p4mO3Anomalyac = mod2([x + y for x, y in zip(p4mO3Anomalya, p4mO3Anomalyc)])
p4mO3Anomalybc = mod2([x + y for x, y in zip(p4mO3Anomalyb, p4mO3Anomalyc)])
p4mO3Anomalyabc = mod2([x + y + z for x, y, z in zip(p4mO3Anomalya, p4mO3Anomalyb, p4mO3Anomalyc)])

def p4mO3AnomalyCheck(multiply_func, homotopylist):
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

    for i in range(2**11):
        for j in range(2**11):
            SFCe = _int_digits(i, 11)
            SFCm = _int_digits(j, 11)
            Anomaly = multiply_func(SFCe, SFCm)
            
            for k in range(len(homotopylist)):
                if Anomaly == matchinganomaly[k]:
                    result[k].append([SFCe, SFCm])
                    break
    return result

def p4mO3Generate(Action, homotopylist):
    if Action == 1:
        result = p4mO3AnomalyCheck(p4mO3Multiply1, homotopylist)
    elif Action == 2:
        result = p4mO3AnomalyCheck(p4mO3Multiply2, homotopylist)
        for i in range(len(homotopylist)):
            addList = []
            for j in range(len(result[i])):
                e0, e1 = result[i][j][0][0], result[i][j][0][1]
                if e0 == 0 and e1 == 0:
                    add1 = [[x for x in result[i][j][0]], [x for x in result[i][j][1]]]
                    add1[0][0] = 2; addList.append(add1)
                    add2 = [[x for x in result[i][j][0]], [x for x in result[i][j][1]]]
                    add2[0][1] = 2; addList.append(add2)
                    add3 = [[x for x in result[i][j][0]], [x for x in result[i][j][1]]]
                    add3[0][0] = 2; add3[0][1] = 2; addList.append(add3)
                if e0 == 0 and e1 == 1:
                    add = [[x for x in result[i][j][0]], [x for x in result[i][j][1]]]
                    add[0][0] = 2; addList.append(add)
                if e0 == 1 and e1 == 0:
                    add = [[x for x in result[i][j][0]], [x for x in result[i][j][1]]]
                    add[0][1] = 2; addList.append(add)
                if e0 == 1 and e1 == 1:
                    add = [[x for x in result[i][j][0]], [x for x in result[i][j][1]]]
                    add[0][0] = 3; addList.append(add)
            result[i] = result[i] + addList
    elif Action == 3:
        result = p4mO3AnomalyCheck(p4mO3Multiply3, homotopylist)
    elif Action == 4:
        result = p4mO3AnomalyCheck(p4mO3Multiply4, homotopylist)
    elif Action == 5:
        result = p4mO3AnomalyCheck(p4mO3Multiply5, homotopylist)
    elif Action == 6:
        result = p4mO3AnomalyCheck(p4mO3Multiply6, homotopylist)
        for i in range(len(homotopylist)):
            addList = []
            for j in range(len(result[i])):
                if result[i][j][0][0] == 0:
                    add = [[x for x in result[i][j][0]], [x for x in result[i][j][1]]]
                    add[0][0] = 2; addList.append(add)
            result[i] = result[i] + addList
    elif Action == 7:
        result = p4mO3AnomalyCheck(p4mO3Multiply7, homotopylist)
        for i in range(len(homotopylist)):
            addList = []
            for j in range(len(result[i])):
                if result[i][j][0][0] == 0:
                    add = [[x for x in result[i][j][0]], [x for x in result[i][j][1]]]
                    add[0][0] = 2; addList.append(add)
            result[i] = result[i] + addList
    elif Action == 8:
        result = p4mO3AnomalyCheck(p4mO3Multiply8, homotopylist)
    return result

def p4mO3CheckSF(Action, SFCe, SFCm):
    if Action == 1: Anomaly = p4mO3Multiply1(SFCe, SFCm)
    elif Action == 2: Anomaly = p4mO3Multiply2(SFCe, SFCm)
    elif Action == 3: Anomaly = p4mO3Multiply3(SFCe, SFCm)
    elif Action == 4: Anomaly = p4mO3Multiply4(SFCe, SFCm)
    elif Action == 5: Anomaly = p4mO3Multiply5(SFCe, SFCm)
    elif Action == 6: Anomaly = p4mO3Multiply6(SFCe, SFCm)
    elif Action == 7: Anomaly = p4mO3Multiply7(SFCe, SFCm)
    elif Action == 8: Anomaly = p4mO3Multiply8(SFCe, SFCm)
    
    if Anomaly == p4mO3Anomaly0: return "0"
    elif Anomaly == p4mO3Anomalya: return "a"
    elif Anomaly == p4mO3Anomalyb: return "b"
    elif Anomaly == p4mO3Anomalyc: return "c"
    elif Anomaly == p4mO3Anomalyab: return "a+b"
    elif Anomaly == p4mO3Anomalyac: return "a+c"
    elif Anomaly == p4mO3Anomalybc: return "b+c"
    elif Anomaly == p4mO3Anomalyabc: return "a+b+c"
    return "empty"


def p4mZ2Multiply(g1, g2):
    return mod2([
        g1[0]*g2[0] + g1[0]*g2[1] + g1[1]*g2[0],
        g1[0]*g2[2] + g1[0]*g2[3] + g1[0]*g2[4] + g1[0]*g2[6] + g1[0]*g2[7] + g1[1]*g2[2] + g1[1]*g2[3] + g1[1]*g2[6] + g1[2]*g2[0] + g1[2]*g2[1] + g1[3]*g2[0] + g1[3]*g2[1] + g1[4]*g2[0] + g1[6]*g2[0] + g1[6]*g2[1] + g1[7]*g2[0],
        g1[0]*g2[2] + g1[0]*g2[3] + g1[0]*g2[5] + g1[0]*g2[6] + g1[0]*g2[8] + g1[1]*g2[2] + g1[1]*g2[3] + g1[1]*g2[6] + g1[2]*g2[0] + g1[2]*g2[1] + g1[3]*g2[0] + g1[3]*g2[1] + g1[5]*g2[0] + g1[6]*g2[0] + g1[6]*g2[1] + g1[8]*g2[0],
        g1[1]*g2[1],
        g1[1]*g2[4] + g1[1]*g2[7] + g1[4]*g2[1] + g1[7]*g2[1],
        g1[1]*g2[5] + g1[1]*g2[8] + g1[5]*g2[1] + g1[8]*g2[1],
        g1[1]*g2[2] + g1[1]*g2[6] + g1[2]*g2[1] + g1[2]*g2[2] + g1[2]*g2[6] + g1[6]*g2[1] + g1[6]*g2[2],
        g1[1]*g2[2] + g1[1]*g2[3] + g1[1]*g2[6] + g1[2]*g2[1] + g1[2]*g2[3] + g1[2]*g2[6] + g1[3]*g2[1] + g1[3]*g2[2] + g1[6]*g2[1] + g1[6]*g2[2],
        g1[1]*g2[3] + g1[2]*g2[5] + g1[3]*g2[1] + g1[3]*g2[3] + g1[3]*g2[8] + g1[5]*g2[2] + g1[5]*g2[6] + g1[6]*g2[5] + g1[8]*g2[3],
        g1[3]*g2[5] + g1[3]*g2[8] + g1[5]*g2[3] + g1[5]*g2[6] + g1[6]*g2[5] + g1[8]*g2[3],
        g1[4]*g2[4] + g1[4]*g2[5] + g1[5]*g2[4],
        g1[5]*g2[5],
        g1[0]*g2[9] + g1[9]*g2[0],
        g1[1]*g2[9] + g1[9]*g2[1],
        g1[2]*g2[9] + g1[6]*g2[6] + g1[6]*g2[9] + g1[9]*g2[2] + g1[9]*g2[6],
        g1[3]*g2[9] + g1[6]*g2[8] + g1[6]*g2[9] + g1[8]*g2[6] + g1[9]*g2[3] + g1[9]*g2[6],
        g1[4]*g2[9] + g1[7]*g2[7] + g1[7]*g2[8] + g1[8]*g2[7] + g1[9]*g2[4],
        g1[5]*g2[9] + g1[8]*g2[8] + g1[9]*g2[5],
        g1[9]*g2[9]
    ])

def p4mZ2Multiply1(g1, g2):
    return mod2([x + y for x, y in zip(
        p4mZ2Multiply([g1[0], g1[1], 0, g1[3], 0, 0, g1[6], g1[7], g1[8], 0], [0, 0, g2[6], g2[6], 0, 0, g2[6], g2[7], g2[8], 0]),
        p4mZ2Multiply([0, 0, g1[2], 0, g1[4], g1[5], 0, 0, 0, g1[9]], [g2[0], g2[1], g2[2], g2[3], g2[4], g2[5], 0, 0, 0, g2[9]])
    )])

def p4mZ2Multiply2(g1, g2):
    return mod2([x + y for x, y in zip(
        p4mZ2Multiply([0, 0, 0, g1[3], g1[4], g1[5], g1[6], g1[7], g1[8], 0], [0, 0, g2[6], 0, g2[7], g2[8], g2[6], g2[7], g2[8], 0]),
        p4mZ2Multiply([g1[0], g1[1], g1[2], g1[2], 0, 0, 0, 0, g1[9], g1[9]], [g2[0], g2[1], g2[2], g2[3], g2[4], g2[5], 0, 0, 0, g2[9]])
    )])

def p4mZ2Multiply3(g1, g2):
    return mod2([x + y for x, y in zip(
        p4mZ2Multiply([g1[0], g1[1], 0, g1[3], 0, g1[5], g1[6], g1[7], g1[8], 0], [0, 0, g2[6], g2[6], g2[7]+g2[8], 0, g2[6], g2[7], g2[8], 0]),
        p4mZ2Multiply([0, 0, g1[2], 0, g1[4], g1[4], 0, g1[9], 0, g1[9]], [g2[0], g2[1], g2[2], g2[3], g2[4], g2[5], 0, 0, 0, g2[9]])
    )])

def p4mZ2Multiply4(g1, g2):
    return mod2([x + y for x, y in zip(
        p4mZ2Multiply([g1[0], g1[1], 0, g1[3], 0, g1[5], g1[6], g1[7], g1[8], 0], [0, 0, g2[6], 0, g2[8], g2[8], g2[6], g2[7], g2[8], 0]),
        p4mZ2Multiply([0, 0, g1[2], g1[2], g1[4], 0, 0, g1[9], g1[9], g1[9]], [g2[0], g2[1], g2[2], g2[3], g2[4], g2[5], 0, 0, 0, g2[9]])
    )])

def p4mZ2Multiply5(g1, g2):
    return mod2([x + y for x, y in zip(
        p4mZ2Multiply([g1[0], g1[1], g1[2], g1[3], 0, 0, g1[6], g1[7], g1[8], 0], [0, 0, 0, g2[6]+g2[8], 0, 0, g2[6], g2[7], g2[8], 0]),
        p4mZ2Multiply([0, 0, 0, g1[5], g1[4], g1[5], g1[9], 0, 0, g1[9]], [g2[0], g2[1], g2[2], g2[3], g2[4], g2[5], 0, 0, 0, g2[9]])
    )])

def p4mZ2Multiply6(g1, g2):
    return mod2([x + y for x, y in zip(
        p4mZ2Multiply([0, g1[1], g1[2], 0, g1[4], g1[5], g1[6], g1[7], g1[8], 0], [0, 0, 0, g2[8], g2[7], g2[8], g2[6], g2[7], g2[8], 0]),
        p4mZ2Multiply([g1[0], g1[0], g1[0], g1[0]+g1[3], 0, 0, g1[9], 0, g1[9], g1[9]], [g2[0], g2[1], g2[2], g2[3], g2[4], g2[5], 0, 0, 0, g2[9]])
    )])

def p4mZ2Multiply7(g1, g2):
    return mod2([x + y for x, y in zip(
        p4mZ2Multiply([0, g1[1], g1[2], g1[3], g1[4], 0, g1[6], g1[7], g1[8], 0], [0, 0, 0, g2[6]+g2[8], g2[7]+g2[8], 0, g2[6], g2[7], g2[8], 0]),
        p4mZ2Multiply([g1[0], 0, 0, g1[5], g1[5], g1[5], g1[9], g1[9], 0, g1[9]], [g2[0], g2[1], g2[2], g2[3], g2[4], g2[5], 0, 0, 0, g2[9]])
    )])

def p4mZ2Multiply8(g1, g2):
    return mod2([x + y for x, y in zip(
        p4mZ2Multiply([g1[0], g1[1], g1[2], 0, 0, g1[5], g1[6], g1[7], g1[8], 0], [0, 0, 0, g2[8], g2[8], g2[8], g2[6], g2[7], g2[8], 0]),
        p4mZ2Multiply([0, 0, 0, g1[3], g1[3]+g1[4], 0, g1[9], g1[9], g1[9], g1[9]], [g2[0], g2[1], g2[2], g2[3], g2[4], g2[5], 0, 0, 0, g2[9]])
    )])

p4mZ2Anomaly0 = [0]*19
p4mZ2Anomalya = [0]*19
p4mZ2Anomalya[12] = 1; p4mZ2Anomalya[13] = 1; p4mZ2Anomalya[14] = 1; p4mZ2Anomalya[15] = 1
p4mZ2Anomalyb = [0]*19
p4mZ2Anomalyb[12] = 1
p4mZ2Anomalyc = [0]*19
p4mZ2Anomalyc[14] = 1; p4mZ2Anomalyc[15] = 1

p4mZ2Anomalyab = mod2([x + y for x, y in zip(p4mZ2Anomalya, p4mZ2Anomalyb)])
p4mZ2Anomalyac = mod2([x + y for x, y in zip(p4mZ2Anomalya, p4mZ2Anomalyc)])
p4mZ2Anomalybc = mod2([x + y for x, y in zip(p4mZ2Anomalyb, p4mZ2Anomalyc)])
p4mZ2Anomalyabc = mod2([x + y + z for x, y, z in zip(p4mZ2Anomalya, p4mZ2Anomalyb, p4mZ2Anomalyc)])

def p4mZ2AnomalyCheck(multiply_func, homotopylist):
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

    for i in range(2**10):
        for j in range(2**10):
            SFCe = _int_digits(i, 10)
            SFCm = _int_digits(j, 10)
            Anomaly = multiply_func(SFCe, SFCm)
            
            for k in range(len(homotopylist)):
                if Anomaly == matchinganomaly[k]:
                    result[k].append([SFCe, SFCm])
                    break
    return result

def p4mZ2Generate(Action, homotopylist):
    if Action == 1:
        result = p4mZ2AnomalyCheck(p4mZ2Multiply1, homotopylist)
    elif Action == 2:
        result = p4mZ2AnomalyCheck(p4mZ2Multiply2, homotopylist)
        for i in range(len(homotopylist)):
            addList = []
            for j in range(len(result[i])):
                e0, e1 = result[i][j][0][0], result[i][j][0][1]
                if e0 == 0 and e1 == 0:
                    add1 = [[x for x in result[i][j][0]], [x for x in result[i][j][1]]]
                    add1[0][0] = 2; addList.append(add1)
                    add2 = [[x for x in result[i][j][0]], [x for x in result[i][j][1]]]
                    add2[0][1] = 2; addList.append(add2)
                    add3 = [[x for x in result[i][j][0]], [x for x in result[i][j][1]]]
                    add3[0][0] = 2; add3[0][1] = 2; addList.append(add3)
                if e0 == 0 and e1 == 1:
                    add = [[x for x in result[i][j][0]], [x for x in result[i][j][1]]]
                    add[0][0] = 2; addList.append(add)
                if e0 == 1 and e1 == 0:
                    add = [[x for x in result[i][j][0]], [x for x in result[i][j][1]]]
                    add[0][1] = 2; addList.append(add)
                if e0 == 1 and e1 == 1:
                    add = [[x for x in result[i][j][0]], [x for x in result[i][j][1]]]
                    add[0][0] = 3; addList.append(add)
            result[i] = result[i] + addList
    elif Action == 3:
        result = p4mZ2AnomalyCheck(p4mZ2Multiply3, homotopylist)
    elif Action == 4:
        result = p4mZ2AnomalyCheck(p4mZ2Multiply4, homotopylist)
    elif Action == 5:
        result = p4mZ2AnomalyCheck(p4mZ2Multiply5, homotopylist)
    elif Action == 6:
        result = p4mZ2AnomalyCheck(p4mZ2Multiply6, homotopylist)
        for i in range(len(homotopylist)):
            addList = []
            for j in range(len(result[i])):
                if result[i][j][0][0] == 0:
                    add = [[x for x in result[i][j][0]], [x for x in result[i][j][1]]]
                    add[0][0] = 2; addList.append(add)
            result[i] = result[i] + addList
    elif Action == 7:
        result = p4mZ2AnomalyCheck(p4mZ2Multiply7, homotopylist)
        for i in range(len(homotopylist)):
            addList = []
            for j in range(len(result[i])):
                if result[i][j][0][0] == 0:
                    add = [[x for x in result[i][j][0]], [x for x in result[i][j][1]]]
                    add[0][0] = 2; addList.append(add)
            result[i] = result[i] + addList
    elif Action == 8:
        result = p4mZ2AnomalyCheck(p4mZ2Multiply8, homotopylist)
    return result

def p4mZ2CheckSF(Action, SFCe, SFCm):
    if Action == 1: Anomaly = p4mZ2Multiply1(SFCe, SFCm)
    elif Action == 2: Anomaly = p4mZ2Multiply2(SFCe, SFCm)
    elif Action == 3: Anomaly = p4mZ2Multiply3(SFCe, SFCm)
    elif Action == 4: Anomaly = p4mZ2Multiply4(SFCe, SFCm)
    elif Action == 5: Anomaly = p4mZ2Multiply5(SFCe, SFCm)
    elif Action == 6: Anomaly = p4mZ2Multiply6(SFCe, SFCm)
    elif Action == 7: Anomaly = p4mZ2Multiply7(SFCe, SFCm)
    elif Action == 8: Anomaly = p4mZ2Multiply8(SFCe, SFCm)
    
    if Anomaly == p4mZ2Anomaly0: return "0"
    elif Anomaly == p4mZ2Anomalya: return "a"
    elif Anomaly == p4mZ2Anomalyb: return "b"
    elif Anomaly == p4mZ2Anomalyc: return "c"
    elif Anomaly == p4mZ2Anomalyab: return "a+b"
    elif Anomaly == p4mZ2Anomalyac: return "a+c"
    elif Anomaly == p4mZ2Anomalybc: return "b+c"
    elif Anomaly == p4mZ2Anomalyabc: return "a+b+c"
    return "empty"
