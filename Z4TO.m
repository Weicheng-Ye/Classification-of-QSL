(* ::Package:: *)

(* ::Section::Closed:: *)
(*p6m*O(3)T*)


(*Given g1=g1[[1]]*Bxy + g1[[2]]*Ac^2 + g1[[3]]*Ac*Am + g1[[4]]*Am^2 + g1[[5]]*Ac*t + g1[[6]]*Am*t + g1[[7]]*t^2 + g1[[8]]*w2
 g2=g2[[1]]*Bxy + g2[[2]]*Ac^2 + g2[[3]]*Ac*Am + g2[[4]]*Am^2 + g2[[5]]*Ac*t + g2[[6]]*Am*t + g2[[7]]*t^2 + g2[[8]]*w2

Calculate exp(pi*i*g1*g2) in the basis

Bxy*Ac^2, Bxy*Ac*Am, Bxy*Am^2, Ac^4, Ac^3*Am, Ac^2*Am^2, Ac*Am^3, Am^4, Bxy*t^2, Ac^2*t^2, Ac*Am*t^2, Am^2*t^2, Bxy*w2, Ac^2*w2, Ac*Am*w2, Am^2*w2, Ac*w3, Am*w3, t^4, w2*t^2, w2^2
*)
p6mO3Multiply[g1_List, g2_List]:=Mod[{
g1[[1]]*g2[[1]]+g1[[1]]*g2[[2]]+g1[[1]]*g2[[5]]+g1[[2]]*g2[[1]]+g1[[5]]*g2[[1]],
g1[[1]]*g2[[1]]+g1[[1]]*g2[[3]]+g1[[3]]*g2[[1]],
g1[[1]]*g2[[4]]+g1[[1]]*g2[[6]]+g1[[4]]*g2[[1]]+g1[[6]]*g2[[1]],
g1[[2]]*g2[[2]]+g1[[2]]*g2[[5]]+g1[[5]]*g2[[2]],
g1[[2]]*g2[[3]]+g1[[2]]*g2[[5]]+g1[[3]]*g2[[2]]+g1[[5]]*g2[[2]],
g1[[2]]*g2[[4]]+g1[[3]]*g2[[3]]+g1[[3]]*g2[[6]]+g1[[4]]*g2[[2]]+g1[[4]]*g2[[5]]+g1[[5]]*g2[[4]]+g1[[6]]*g2[[3]],
g1[[3]]*g2[[4]]+g1[[3]]*g2[[6]]+g1[[4]]*g2[[3]]+g1[[4]]*g2[[5]]+g1[[5]]*g2[[4]]+g1[[6]]*g2[[3]],
g1[[4]]*g2[[4]],
g1[[1]]*g2[[7]]+g1[[7]]*g2[[1]],
g1[[2]]*g2[[7]]+g1[[5]]*g2[[5]]+g1[[5]]*g2[[7]]+g1[[7]]*g2[[2]]+g1[[7]]*g2[[5]],
g1[[3]]*g2[[7]]+g1[[5]]*g2[[6]]+g1[[5]]*g2[[7]]+g1[[6]]*g2[[5]]+g1[[7]]*g2[[3]]+g1[[7]]*g2[[5]],
g1[[4]]*g2[[7]]+g1[[6]]*g2[[6]]+g1[[7]]*g2[[4]],
g1[[1]]*g2[[8]]+g1[[8]]*g2[[1]],
g1[[2]]*g2[[8]]+g1[[5]]*g2[[8]]+g1[[8]]*g2[[2]]+g1[[8]]*g2[[5]],
g1[[3]]*g2[[8]]+g1[[5]]*g2[[8]]+g1[[8]]*g2[[3]]+g1[[8]]*g2[[5]],
g1[[4]]*g2[[8]]+g1[[8]]*g2[[4]],
g1[[5]]*g2[[8]]+g1[[8]]*g2[[5]],
g1[[6]]*g2[[8]]+g1[[8]]*g2[[6]],
g1[[7]]*g2[[7]],
g1[[7]]*g2[[8]]+g1[[8]]*g2[[7]],
g1[[8]]*g2[[8]]
},2]


p6mO3Multiply1[g1_List,g2_List]:=Mod[p6mO3Multiply[{g1[[1]],0,g1[[3]],0,g1[[5]],g1[[6]],0,g1[[8]]},{0,g2[[5]],g2[[5]],0,g2[[5]],g2[[6]],0,0}]+p6mO3Multiply[{0,g1[[2]],0,g1[[4]],0,0,g1[[7]],0},{g2[[1]],g2[[2]],g2[[3]],g2[[4]],0,0,g2[[7]],g2[[8]]}],2]


p6mO3Multiply2[g1_List,g2_List]:=Mod[p6mO3Multiply[{0,0,g1[[3]],g1[[4]],g1[[5]],g1[[6]],0,g1[[8]]},{0,g2[[5]],0,g2[[6]],g2[[5]],g2[[6]],0,0}]+p6mO3Multiply[{g1[[1]],g1[[2]],g1[[2]],0,0,g1[[7]],g1[[7]],0},{g2[[1]],g2[[2]],g2[[3]],g2[[4]],0,0,g2[[7]],g2[[8]]}],2]


p6mO3Multiply3[g1_List,g2_List]:=Mod[p6mO3Multiply[{g1[[1]],g1[[2]],g1[[3]],0,g1[[5]],g1[[6]],0,g1[[8]]},{0,0,g2[[5]]+g2[[6]],0,g2[[5]],g2[[6]],0,0}]+p6mO3Multiply[{0,0,g1[[4]],g1[[4]],g1[[7]],0,g1[[7]],0},{g2[[1]],g2[[2]],g2[[3]],g2[[4]],0,0,g2[[7]],g2[[8]]}],2]


p6mO3Multiply4[g1_List,g2_List]:=Mod[p6mO3Multiply[{g1[[1]],g1[[2]],0,g1[[4]],g1[[5]],g1[[6]],0,g1[[8]]},{0,0,g2[[6]],g2[[6]],g2[[5]],g2[[6]],0,0}]+p6mO3Multiply[{0,0,g1[[3]],0,g1[[7]],g1[[7]],g1[[7]],0},{g2[[1]],g2[[2]],g2[[3]],g2[[4]],0,0,g2[[7]],g2[[8]]}],2]


p6mO3Anomaly0=ConstantArray[0,21];
p6mO3Anomalya=ConstantArray[0,21];p6mO3Anomalya[[9]]=1;p6mO3Anomalya[[10]]=1;p6mO3Anomalya[[11]]=1;p6mO3Anomalya[[13]]=1;p6mO3Anomalya[[14]]=1;p6mO3Anomalya[[15]]=1;
p6mO3Anomalyc=ConstantArray[0,21];p6mO3Anomalyc[[9]]=1;p6mO3Anomalyc[[13]]=1;
p6mO3Anomalyac=Mod[p6mO3Anomalya+p6mO3Anomalyc,2];


p6mO3AnomalyCheck[multiply_, homotopylist_]:=Module[{result, Anomaly, matchinganomaly, i, j, SFCe, SFCm},
result={};Do[AppendTo[result, {}], {i, 1, Length[homotopylist]}];
matchinganomaly = {};
For[i=1,i<=Length[homotopylist],i++, 
If[homotopylist[[i]]=="0", AppendTo[matchinganomaly, p6mO3Anomaly0];];
If[homotopylist[[i]]=="a", AppendTo[matchinganomaly, p6mO3Anomalya];];
If[homotopylist[[i]]=="c", AppendTo[matchinganomaly, p6mO3Anomalyc];];
If[homotopylist[[i]]=="a+c", AppendTo[matchinganomaly, p6mO3Anomalyac];];];

For[i=0,i<2^8,i++,
For[j=0,j<2^8,j++,
SFCe=PadLeft[IntegerDigits[i,2],8];
SFCm=PadLeft[IntegerDigits[j,2],8];
Anomaly=multiply[SFCe, SFCm];
Do[If[Anomaly==matchinganomaly[[i]], AppendTo[result[[i]], {SFCe, SFCm}];Break[]], {i, 1, Length[homotopylist]}];
]];
result]


p6mO3Generate[Action_, homotopylist_]:=Module[{result, addList, add, i, j},
If[Action==1, result=p6mO3AnomalyCheck[p6mO3Multiply1, homotopylist];];
If[Action==2, result=p6mO3AnomalyCheck[p6mO3Multiply2, homotopylist];
For[i=1, i<=Length[homotopylist], i++,
addList={};
For[j=1, j<=Length[result[[i]]], j++,
If[result[[i]][[j]][[1]][[1]]==0,add=result[[i]][[j]];add[[1]][[1]]=2;AppendTo[addList,add];];];
result[[i]] = Join[result[[i]], addList];
];];
If[Action==3, result=p6mO3AnomalyCheck[p6mO3Multiply3, homotopylist];];
If[Action==4, result=p6mO3AnomalyCheck[p6mO3Multiply4, homotopylist];];
result]


p6mO3CheckSF[Action_, SFCe_, SFCm_]:=Module[{Anomaly, lattice},
If[Action==1, Anomaly=p6mO3Multiply1[SFCe, SFCm];];
If[Action==2, Anomaly=p6mO3Multiply2[SFCe, SFCm];];
If[Action==3, Anomaly=p6mO3Multiply3[SFCe, SFCm];];
If[Action==4, Anomaly=p6mO3Multiply4[SFCe, SFCm];];

lattice = Which[Anomaly==p6mO3Anomaly0, lattice="0", 
				Anomaly==p6mO3Anomalya, lattice="a",
				Anomaly==p6mO3Anomalyc, lattice="c",
				Anomaly==p6mO3Anomalyac, lattice="a+c",
				True, lattice="empty"];

lattice]


(* ::Section::Closed:: *)
(*p6m*Z2T*)


(*Given g1=g1[[1]]*Bxy + g1[[2]]*Ac^2 + g1[[3]]*Ac*Am + g1[[4]]*Am^2 + g1[[5]]*Ac*t + g1[[6]]*Am*t + g1[[7]]*t^2 + g1[[8]]*w2
 g2=g2[[1]]*Bxy + g2[[2]]*Ac^2 + g2[[3]]*Ac*Am + g2[[4]]*Am^2 + g2[[5]]*Ac*t + g2[[6]]*Am*t + g2[[7]]*t^2 + g2[[8]]*w2

Calculate exp(pi*i*g1*g2) in the basis

Bxy*Ac^2, Bxy*Ac*Am, Bxy*Am^2, Ac^4, Ac^3*Am, Ac^2*Am^2, Ac*Am^3, Am^4, Bxy*t^2, Ac^2*t^2, Ac*Am*t^2, Am^2*t^2, t^4
*)
p6mZ2Multiply[g1_List, g2_List]:=Mod[{
g1[[1]]*g2[[1]]+g1[[1]]*g2[[2]]+g1[[1]]*g2[[5]]+g1[[2]]*g2[[1]]+g1[[5]]*g2[[1]],
g1[[1]]*g2[[1]]+g1[[1]]*g2[[3]]+g1[[3]]*g2[[1]],
g1[[1]]*g2[[4]]+g1[[1]]*g2[[6]]+g1[[4]]*g2[[1]]+g1[[6]]*g2[[1]],
g1[[2]]*g2[[2]]+g1[[2]]*g2[[5]]+g1[[5]]*g2[[2]],
g1[[2]]*g2[[3]]+g1[[2]]*g2[[5]]+g1[[3]]*g2[[2]]+g1[[5]]*g2[[2]],
g1[[2]]*g2[[4]]+g1[[3]]*g2[[3]]+g1[[3]]*g2[[6]]+g1[[4]]*g2[[2]]+g1[[4]]*g2[[5]]+g1[[5]]*g2[[4]]+g1[[6]]*g2[[3]],
g1[[3]]*g2[[4]]+g1[[3]]*g2[[6]]+g1[[4]]*g2[[3]]+g1[[4]]*g2[[5]]+g1[[5]]*g2[[4]]+g1[[6]]*g2[[3]],
g1[[4]]*g2[[4]],
g1[[1]]*g2[[7]]+g1[[7]]*g2[[1]],
g1[[2]]*g2[[7]]+g1[[5]]*g2[[5]]+g1[[5]]*g2[[7]]+g1[[7]]*g2[[2]]+g1[[7]]*g2[[5]],
g1[[3]]*g2[[7]]+g1[[5]]*g2[[6]]+g1[[5]]*g2[[7]]+g1[[6]]*g2[[5]]+g1[[7]]*g2[[3]]+g1[[7]]*g2[[5]],
g1[[4]]*g2[[7]]+g1[[6]]*g2[[6]]+g1[[7]]*g2[[4]],
g1[[7]]*g2[[7]]
},2]


p6mZ2Multiply1[g1_List,g2_List]:=Mod[p6mZ2Multiply[{g1[[1]],0,g1[[3]],0,g1[[5]],g1[[6]],0},{0,g2[[5]],g2[[5]],0,g2[[5]],g2[[6]],0}]+p6mZ2Multiply[{0,g1[[2]],0,g1[[4]],0,0,g1[[7]]},{g2[[1]],g2[[2]],g2[[3]],g2[[4]],0,0,g2[[7]]}],2]


p6mZ2Multiply2[g1_List,g2_List]:=Mod[p6mZ2Multiply[{0,0,g1[[3]],g1[[4]],g1[[5]],g1[[6]],0},{0,g2[[5]],0,g2[[6]],g2[[5]],g2[[6]],0}]+p6mZ2Multiply[{g1[[1]],g1[[2]],g1[[2]],0,0,g1[[7]],g1[[7]]},{g2[[1]],g2[[2]],g2[[3]],g2[[4]],0,0,g2[[7]]}],2]


p6mZ2Multiply3[g1_List,g2_List]:=Mod[p6mZ2Multiply[{g1[[1]],g1[[2]],g1[[3]],0,g1[[5]],g1[[6]],0},{0,0,g2[[5]]+g2[[6]],0,g2[[5]],g2[[6]],0}]+p6mZ2Multiply[{0,0,g1[[4]],g1[[4]],g1[[7]],0,g1[[7]]},{g2[[1]],g2[[2]],g2[[3]],g2[[4]],0,0,g2[[7]]}],2]


p6mZ2Multiply4[g1_List,g2_List]:=Mod[p6mZ2Multiply[{g1[[1]],g1[[2]],0,g1[[4]],g1[[5]],g1[[6]],0},{0,0,g2[[6]],g2[[6]],g2[[5]],g2[[6]],0}]+p6mZ2Multiply[{0,0,g1[[3]],0,g1[[7]],g1[[7]],g1[[7]]},{g2[[1]],g2[[2]],g2[[3]],g2[[4]],0,0,g2[[7]]}],2]


p6mZ2Anomaly0=ConstantArray[0,13];
p6mZ2Anomalya=ConstantArray[0,13];p6mZ2Anomalya[[9]]=1;p6mZ2Anomalya[[10]]=1;p6mZ2Anomalya[[11]]=1;
p6mZ2Anomalyc=ConstantArray[0,13];p6mZ2Anomalyc[[9]]=1;
p6mZ2Anomalyac=Mod[p6mZ2Anomalya+p6mZ2Anomalyc,2];


p6mZ2AnomalyCheck[multiply_, homotopylist_]:=Module[{result, Anomaly, matchinganomaly, i, j, SFCe, SFCm},
result={};Do[AppendTo[result, {}], {i, 1, Length[homotopylist]}];
matchinganomaly = {};
For[i=1,i<=Length[homotopylist],i++, 
If[homotopylist[[i]]=="0", AppendTo[matchinganomaly, p6mZ2Anomaly0];];
If[homotopylist[[i]]=="a", AppendTo[matchinganomaly, p6mZ2Anomalya];];
If[homotopylist[[i]]=="c", AppendTo[matchinganomaly, p6mZ2Anomalyc];];
If[homotopylist[[i]]=="a+c", AppendTo[matchinganomaly, p6mZ2Anomalyac];];];

For[i=0,i<2^7,i++,
For[j=0,j<2^7,j++,
SFCe=PadLeft[IntegerDigits[i,2],7];
SFCm=PadLeft[IntegerDigits[j,2],7];
Anomaly=multiply[SFCe, SFCm];
Do[If[Anomaly==matchinganomaly[[i]], AppendTo[result[[i]], {SFCe, SFCm}];Break[]], {i, 1, Length[homotopylist]}];
]];
result]


p6mZ2Generate[Action_, homotopylist_]:=Module[{result, addList, add, i, j},
If[Action==1, result=p6mZ2AnomalyCheck[p6mZ2Multiply1, homotopylist];];
If[Action==2, result=p6mZ2AnomalyCheck[p6mZ2Multiply2, homotopylist];
addList={};
For[i=1, i<=Length[homotopylist], i++,
addList={};
For[j=1, j<=Length[result[[i]]], j++,
If[result[[i]][[j]][[1]][[1]]==0,add=result[[i]][[j]];add[[1]][[1]]=2;AppendTo[addList,add];];];
result[[i]] = Join[result[[i]], addList];
];];
If[Action==3, result=p6mZ2AnomalyCheck[p6mZ2Multiply3, homotopylist];];
If[Action==4, result=p6mZ2AnomalyCheck[p6mZ2Multiply4, homotopylist];];
result]


p6mZ2CheckSF[Action_, SFCe_, SFCm_]:=Module[{Anomaly, lattice},
If[Action==1, Anomaly=p6mZ2Multiply1[SFCe, SFCm];];
If[Action==2, Anomaly=p6mZ2Multiply2[SFCe, SFCm];];
If[Action==3, Anomaly=p6mZ2Multiply3[SFCe, SFCm];];
If[Action==4, Anomaly=p6mZ2Multiply4[SFCe, SFCm];];

lattice = Which[Anomaly==p6mZ2Anomaly0, lattice="0", 
				Anomaly==p6mZ2Anomalya, lattice="a",
				Anomaly==p6mZ2Anomalyc, lattice="c",
				Anomaly==p6mZ2Anomalyac, lattice="a+c",
				True, lattice="empty"];

lattice]


(* ::Section::Closed:: *)
(*p4m*O(3)T*)


(*Given g1=g1[[1]]*Bxy + g1[[2]]*Bc2+ g1[[3]]*Ax+y^2 + g1[[4]]*Ax+y*Am + g1[[5]]*Ac^2 + g1[[6]]*Am^2 + g1[[7]]*Ax+y*t+g1[[8]]*Ac*t + g1[[9]]*Am*t + g1[[10]]*t^2 + g1[[11]]*w2
g2[[1]]*Bxy + g2[[2]]*Bc2+ g2[[3]]*Ax+y^2 + g2[[4]]*Ax+y*Am + g2[[5]]*Ac^2 + g2[[6]]*Am^2 + g2[[7]]*Ax+y*t+g2[[8]]*Ac*t + g2[[9]]*Am*t + g2[[10]]*t^2 + g2[[11]]*w2

Calculate exp(pi*i*g1*g2) in the basis

Bxy*Bc2, Bxy*Ac^2, Bxy*Am^2, Bc2^2, Bc2*Ac^2, Bc2*Am^2, Ax+y^4, Ax+y^3*Am, Ax+y^2*Am^2, Ax+y*Am^3,Ac^4, Am^4, 
Bxy*t^2, Bc2*t^2, Ax+y^2*t^2, Ax+y*Am*t^2, Ac^2*t^2,  Am^2*t^2, Bxy*w2, Bc2*w2, Ax+y^2*w2, Ax+y*Am*w2, Ac^2*w2, Am^2*w2, Ax+y*w3, Ac*w3, Am*w3, t^4, w2*t^2, w2^2
*)
p4mO3Multiply[g1_List, g2_List]:=Mod[{
g1[[1]]*g2[[1]]+g1[[1]]*g2[[2]]+g1[[2]]*g2[[1]],
g1[[1]]*g2[[3]]+g1[[1]]*g2[[4]]+g1[[1]]*g2[[5]]+g1[[1]]*g2[[7]]+g1[[1]]*g2[[8]]+g1[[2]]*g2[[3]]+g1[[2]]*g2[[4]]+g1[[2]]*g2[[7]]+g1[[3]]*g2[[1]]+g1[[3]]*g2[[2]]+g1[[4]]*g2[[1]]+g1[[4]]*g2[[2]]+g1[[5]]*g2[[1]]+g1[[7]]*g2[[1]]+g1[[7]]*g2[[2]]+g1[[8]]*g2[[1]],
g1[[1]]*g2[[3]]+g1[[1]]*g2[[4]]+g1[[1]]*g2[[6]]+g1[[1]]*g2[[7]]+g1[[1]]*g2[[9]]+g1[[2]]*g2[[3]]+g1[[2]]*g2[[4]]+g1[[2]]*g2[[7]]+g1[[3]]*g2[[1]]+g1[[3]]*g2[[2]]+g1[[4]]*g2[[1]]+g1[[4]]*g2[[2]]+g1[[6]]*g2[[1]]+g1[[7]]*g2[[1]]+g1[[7]]*g2[[2]]+g1[[9]]*g2[[1]],
g1[[2]]*g2[[2]],
g1[[2]]*g2[[5]]+g1[[2]]*g2[[8]]+g1[[5]]*g2[[2]]+g1[[8]]*g2[[2]],
g1[[2]]*g2[[6]]+g1[[2]]*g2[[9]]+g1[[6]]*g2[[2]]+g1[[9]]*g2[[2]],
g1[[2]]*g2[[3]]+g1[[2]]*g2[[7]]+g1[[3]]*g2[[2]]+g1[[3]]*g2[[3]]+g1[[3]]*g2[[7]]+g1[[7]]*g2[[2]]+g1[[7]]*g2[[3]],
g1[[2]]*g2[[3]]+g1[[2]]*g2[[4]]+g1[[2]]*g2[[7]]+g1[[3]]*g2[[2]]+g1[[3]]*g2[[4]]+g1[[3]]*g2[[7]]+g1[[4]]*g2[[2]]+g1[[4]]*g2[[3]]+g1[[7]]*g2[[2]]+g1[[7]]*g2[[3]],
g1[[2]]*g2[[4]]+g1[[3]]*g2[[6]]+g1[[4]]*g2[[2]]+g1[[4]]*g2[[4]]+g1[[4]]*g2[[9]]+g1[[6]]*g2[[3]]+g1[[6]]*g2[[7]]+g1[[7]]*g2[[6]]+g1[[9]]*g2[[4]],
g1[[4]]*g2[[6]]+g1[[4]]*g2[[9]]+g1[[6]]*g2[[4]]+g1[[6]]*g2[[7]]+g1[[7]]*g2[[6]]+g1[[9]]*g2[[4]],
g1[[5]]*g2[[5]]+g1[[5]]*g2[[6]]+g1[[6]]*g2[[5]],
g1[[6]]*g2[[6]],
g1[[1]]*g2[[10]]+g1[[10]]*g2[[1]],
g1[[2]]*g2[[10]]+g1[[10]]*g2[[2]],
g1[[3]]*g2[[10]]+g1[[7]]*g2[[7]]+g1[[7]]*g2[[10]]+g1[[10]]*g2[[3]]+g1[[10]]*g2[[7]],
g1[[4]]*g2[[10]]+g1[[7]]*g2[[9]]+g1[[7]]*g2[[10]]+g1[[9]]*g2[[7]]+g1[[10]]*g2[[4]]+g1[[10]]*g2[[7]],
g1[[5]]*g2[[10]]+g1[[8]]*g2[[8]]+g1[[8]]*g2[[9]]+g1[[9]]*g2[[8]]+g1[[10]]*g2[[5]],
g1[[6]]*g2[[10]]+g1[[9]]*g2[[9]]+g1[[10]]*g2[[6]],
g1[[1]]*g2[[11]]+g1[[11]]*g2[[1]],
g1[[2]]*g2[[11]]+g1[[11]]*g2[[2]],
g1[[3]]*g2[[11]]+g1[[7]]*g2[[11]]+g1[[11]]*g2[[3]]+g1[[11]]*g2[[7]],
g1[[4]]*g2[[11]]+g1[[7]]*g2[[11]]+g1[[11]]*g2[[4]]+g1[[11]]*g2[[7]],
g1[[5]]*g2[[11]]+g1[[11]]*g2[[5]],
g1[[6]]*g2[[11]]+g1[[11]]*g2[[6]],
g1[[7]]*g2[[11]]+g1[[11]]*g2[[7]],
g1[[8]]*g2[[11]]+g1[[11]]*g2[[8]],
g1[[9]]*g2[[11]]+g1[[11]]*g2[[9]],
g1[[10]]*g2[[10]],
g1[[10]]*g2[[11]]+g1[[11]]*g2[[10]],
g1[[11]]*g2[[11]]
},2]


p4mO3Multiply1[g1_List,g2_List]:=Mod[p4mO3Multiply[{g1[[1]],g1[[2]],0,g1[[4]],0,0,g1[[7]],g1[[8]],g1[[9]],0,g1[[11]]},{0,0,g2[[7]],g2[[7]],0,0,g2[[7]],g2[[8]],g2[[9]],0,0}]+
p4mO3Multiply[{0,0,g1[[3]],0,g1[[5]],g1[[6]],0,0,0,g1[[10]],0},{g2[[1]],g2[[2]],g2[[3]],g2[[4]],g2[[5]],g2[[6]],0,0,0,g2[[10]],g2[[11]]}],2]


p4mO3Multiply2[g1_List,g2_List]:=Mod[p4mO3Multiply[{0,0,0,g1[[4]],g1[[5]],g1[[6]],g1[[7]],g1[[8]],g1[[9]],0,g1[[11]]},{0,0,g2[[7]],0,g2[[8]],g2[[9]],g2[[7]],g2[[8]],g2[[9]],0,0}]+
p4mO3Multiply[{g1[[1]],g1[[2]],g1[[3]],g1[[3]],0,0,0,0,g1[[10]],g1[[10]],0},{g2[[1]],g2[[2]],g2[[3]],g2[[4]],g2[[5]],g2[[6]],0,0,0,g2[[10]],g2[[11]]}],2]


p4mO3Multiply3[g1_List,g2_List]:=Mod[p4mO3Multiply[{g1[[1]],g1[[2]],0,g1[[4]],0,g1[[6]],g1[[7]],g1[[8]],g1[[9]],0,g1[[11]]},{0,0,g2[[7]],g2[[7]],g2[[8]]+g2[[9]],0,g2[[7]],g2[[8]],g2[[9]],0,0}]+
p4mO3Multiply[{0,0,g1[[3]],0,g1[[5]],g1[[5]],0,g1[[10]],0,g1[[10]],0},{g2[[1]],g2[[2]],g2[[3]],g2[[4]],g2[[5]],g2[[6]],0,0,0,g2[[10]],g2[[11]]}],2]


p4mO3Multiply4[g1_List,g2_List]:=Mod[p4mO3Multiply[{g1[[1]],g1[[2]],0,g1[[4]],0,g1[[6]],g1[[7]],g1[[8]],g1[[9]],0,g1[[11]]},{0,0,g2[[7]],0,g2[[9]],g2[[9]],g2[[7]],g2[[8]],g2[[9]],0,0}]+
p4mO3Multiply[{0,0,g1[[3]],g1[[3]],g1[[5]],0,0,g1[[10]],g1[[10]],g1[[10]],0},{g2[[1]],g2[[2]],g2[[3]],g2[[4]],g2[[5]],g2[[6]],0,0,0,g2[[10]],g2[[11]]}],2]


p4mO3Multiply5[g1_List,g2_List]:=Mod[p4mO3Multiply[{g1[[1]],g1[[2]],g1[[3]],g1[[4]],0,0,g1[[7]],g1[[8]],g1[[9]],0,g1[[11]]},{0,0,0,g2[[7]]+g2[[9]],0,0,g2[[7]],g2[[8]],g2[[9]],0,0}]+
p4mO3Multiply[{0,0,0,g1[[6]],g1[[5]],g1[[6]],g1[[10]],0,0,g1[[10]],0},{g2[[1]],g2[[2]],g2[[3]],g2[[4]],g2[[5]],g2[[6]],0,0,0,g2[[10]],g2[[11]]}],2]


p4mO3Multiply6[g1_List,g2_List]:=Mod[p4mO3Multiply[{0,g1[[2]],g1[[3]],0,g1[[5]],g1[[6]],g1[[7]],g1[[8]],g1[[9]],0,g1[[11]]},{0,0,0,g2[[9]],g2[[8]],g2[[9]],g2[[7]],g2[[8]],g2[[9]],0,0}]+
p4mO3Multiply[{g1[[1]],g1[[1]],g1[[1]],g1[[1]]+g1[[4]],0,0,g1[[10]],0,g1[[10]],g1[[10]],0},{g2[[1]],g2[[2]],g2[[3]],g2[[4]],g2[[5]],g2[[6]],0,0,0,g2[[10]],g2[[11]]}],2]


p4mO3Multiply7[g1_List,g2_List]:=Mod[p4mO3Multiply[{0,g1[[2]],g1[[3]],g1[[4]],g1[[5]],0,g1[[7]],g1[[8]],g1[[9]],0,g1[[11]]},{0,0,0,g2[[7]]+g2[[9]],g2[[8]]+g2[[9]],0,g2[[7]],g2[[8]],g2[[9]],0,0}]+
p4mO3Multiply[{g1[[1]],0,0,g1[[6]],g1[[6]],g1[[6]],g1[[10]],g1[[10]],0,g1[[10]],0},{g2[[1]],g2[[2]],g2[[3]],g2[[4]],g2[[5]],g2[[6]],0,0,0,g2[[10]],g2[[11]]}],2]


p4mO3Multiply8[g1_List,g2_List]:=Mod[p4mO3Multiply[{g1[[1]],g1[[2]],g1[[3]],0,0,g1[[6]],g1[[7]],g1[[8]],g1[[9]],0,g1[[11]]},{0,0,0,g2[[9]],g2[[9]],g2[[9]],g2[[7]],g2[[8]],g2[[9]],0,0}]+
p4mO3Multiply[{0,0,0,g1[[4]],g1[[4]]+g1[[5]],0,g1[[10]],g1[[10]],g1[[10]],g1[[10]],0},{g2[[1]],g2[[2]],g2[[3]],g2[[4]],g2[[5]],g2[[6]],0,0,0,g2[[10]],g2[[11]]}],2]


p4mO3Anomaly0=ConstantArray[0,30];
p4mO3Anomalya=ConstantArray[0,30];p4mO3Anomalya[[13]]=1;p4mO3Anomalya[[14]]=1;p4mO3Anomalya[[15]]=1;p4mO3Anomalya[[16]]=1;p4mO3Anomalya[[19]]=1;p4mO3Anomalya[[20]]=1;p4mO3Anomalya[[21]]=1;p4mO3Anomalya[[22]]=1;
p4mO3Anomalyb=ConstantArray[0,30];p4mO3Anomalyb[[13]]=1;p4mO3Anomalyb[[19]]=1;
p4mO3Anomalyc=ConstantArray[0,30];p4mO3Anomalyc[[15]]=1;p4mO3Anomalyc[[16]]=1;p4mO3Anomalyc[[21]]=1;p4mO3Anomalyc[[22]]=1;

p4mO3Anomalyab=Mod[p4mO3Anomalya+p4mO3Anomalyb,2];
p4mO3Anomalyac=Mod[p4mO3Anomalya+p4mO3Anomalyc,2];
p4mO3Anomalybc=Mod[p4mO3Anomalyb+p4mO3Anomalyc,2];
p4mO3Anomalyabc=Mod[p4mO3Anomalya+p4mO3Anomalyb+p4mO3Anomalyc,2];


p4mO3AnomalyCheck[multiply_, homotopylist_]:=Module[{result, Anomaly, matchinganomaly, i, j, SFCe, SFCm},
result={};Do[AppendTo[result, {}], {i, 1, Length[homotopylist]}];
matchinganomaly = {};
For[i=1,i<=Length[homotopylist],i++, 
If[homotopylist[[i]]=="0", AppendTo[matchinganomaly, p4mO3Anomaly0];];
If[homotopylist[[i]]=="a", AppendTo[matchinganomaly, p4mO3Anomalya];];
If[homotopylist[[i]]=="b", AppendTo[matchinganomaly, p4mO3Anomalyb];];
If[homotopylist[[i]]=="c", AppendTo[matchinganomaly, p4mO3Anomalyc];];
If[homotopylist[[i]]=="a+b", AppendTo[matchinganomaly, p4mO3Anomalyab];];
If[homotopylist[[i]]=="a+c", AppendTo[matchinganomaly, p4mO3Anomalyac];];
If[homotopylist[[i]]=="b+c", AppendTo[matchinganomaly, p4mO3Anomalybc];];
If[homotopylist[[i]]=="a+b+c", AppendTo[matchinganomaly, p4mO3Anomalyabc];];];

For[i=0,i<2^11,i++,
For[j=0,j<2^11,j++,
SFCe=PadLeft[IntegerDigits[i,2],11];
SFCm=PadLeft[IntegerDigits[j,2],11];
Anomaly=multiply[SFCe, SFCm];
Do[If[Anomaly==matchinganomaly[[i]], AppendTo[result[[i]], {SFCe, SFCm}];Break[]], {i, 1, Length[homotopylist]}];
]];
result]


p4mO3Generate[Action_, homotopylist_]:=Module[{result, addList, add, i, j},
If[Action==1, result=p4mO3AnomalyCheck[p4mO3Multiply1, homotopylist];];
If[Action==2, result=p4mO3AnomalyCheck[p4mO3Multiply2, homotopylist];
For[i=1, i<=Length[homotopylist], i++,
addList = {};
For[j=1, j<=Length[result[[i]]], j++,

If[(result[[i]][[j]][[1]][[1]]==0)&&(result[[i]][[j]][[1]][[2]]==0),
add=result[[i]][[j]];add[[1]][[1]]=2;AppendTo[addList,add];
add=result[[i]][[j]];add[[1]][[2]]=2;AppendTo[addList,add];
add=result[[i]][[j]];add[[1]][[1]]=2;add[[1]][[2]]=2;AppendTo[addList,add];];

If[(result[[i]][[j]][[1]][[1]]==0)&&(result[[i]][[j]][[1]][[2]]==1),
add=result[[i]][[j]];add[[1]][[1]]=2;AppendTo[addList,add];];

If[(result[[i]][[j]][[1]][[1]]==1)&&(result[[i]][[j]][[1]][[2]]==0),
add=result[[i]][[j]];add[[1]][[2]]=2;AppendTo[addList,add];];

If[(result[[i]][[j]][[1]][[1]]==1)&&(result[[i]][[j]][[1]][[2]]==1),
add=result[[i]][[j]];add[[1]][[1]]=3;AppendTo[addList,add];];];

result[[i]] = Join[result[[i]], addList];
];];
If[Action==3, result=p4mO3AnomalyCheck[p4mO3Multiply3, homotopylist];];
If[Action==4, result=p4mO3AnomalyCheck[p4mO3Multiply4, homotopylist];];
If[Action==5, result=p4mO3AnomalyCheck[p4mO3Multiply5, homotopylist];];
If[Action==6, result=p4mO3AnomalyCheck[p4mO3Multiply6, homotopylist];
For[i=1, i<=Length[homotopylist], i++,
addList = {};
For[j=1, j<=Length[result[[i]]], j++,
If[result[[i]][[j]][[1]][[1]]==0,add=result[[i]][[j]];add[[1]][[1]]=2;AppendTo[addList,add];]];
result[[i]] = Join[result[[i]], addList];
]];
If[Action==7, result=p4mO3AnomalyCheck[p4mO3Multiply7, homotopylist];
For[i=1, i<=Length[homotopylist], i++,
addList = {};
For[j=1, j<=Length[result[[i]]], j++,
If[result[[i]][[j]][[1]][[1]]==0,add=result[[i]][[j]];add[[1]][[1]]=2;AppendTo[addList,add];]];
result[[i]] = Join[result[[i]], addList];
]];
If[Action==8, result=p4mO3AnomalyCheck[p4mO3Multiply8, homotopylist];];
result]


p4mO3CheckSF[Action_, SFCe_, SFCm_]:=Module[{Anomaly, lattice},

If[Action==1, Anomaly=p4mO3Multiply1[SFCe, SFCm];];
If[Action==2, Anomaly=p4mO3Multiply2[SFCe, SFCm];];
If[Action==3, Anomaly=p4mO3Multiply3[SFCe, SFCm];];
If[Action==4, Anomaly=p4mO3Multiply4[SFCe, SFCm];];
If[Action==5, Anomaly=p4mO3Multiply5[SFCe, SFCm];];
If[Action==6, Anomaly=p4mO3Multiply6[SFCe, SFCm];];
If[Action==7, Anomaly=p4mO3Multiply7[SFCe, SFCm];];
If[Action==8, Anomaly=p4mO3Multiply8[SFCe, SFCm];];


lattice = Which[Anomaly==p4mO3Anomaly0, lattice="0", 
				Anomaly==p4mO3Anomalya, lattice="a",
				Anomaly==p4mO3Anomalyb, lattice="b",
				Anomaly==p4mO3Anomalyc, lattice="c",
				Anomaly==p4mO3Anomalyab, lattice="a+b", 
				Anomaly==p4mO3Anomalyac, lattice="a+c",
				Anomaly==p4mO3Anomalybc, lattice="b+c",
				Anomaly==p4mO3Anomalyabc, lattice="a+b+c",
				True, lattice="empty"];

lattice]


(* ::Section::Closed:: *)
(*p4m*Z2T*)


(*Given g1=g1[[1]]*Bxy + g1[[2]]*Bc2+ g1[[3]]*Ax+y^2 + g1[[4]]*Ax+y*Am + g1[[5]]*Ac^2 + g1[[6]]*Am^2 + g1[[7]]*Ax+y*t+g1[[8]]*Ac*t + g1[[9]]*Am*t + g1[[10]]*t^2
g2[[1]]*Bxy + g2[[2]]*Bc2+ g2[[3]]*Ax+y^2 + g2[[4]]*Ax+y*Am + g2[[5]]*Ac^2 + g2[[6]]*Am^2 + g2[[7]]*Ax+y*t+g2[[8]]*Ac*t + g2[[9]]*Am*t + g2[[10]]*t^2

Calculate exp(pi*i*g1*g2) in the basis

Bxy*Bc2, Bxy*Ac^2, Bxy*Am^2, Bc2^2, Bc2*Ac^2, Bc2*Am^2, Ax+y^4, Ax+y^3*Am, Ax+y^2*Am^2, Ax+y*Am^3,Ac^4, Am^4, Bxy*t^2, Bc2*t^2, Ax+y^2*t^2, Ax+y*Am*t^2, Ac^2*t^2,  Am^2*t^2, t^4
*)
p4mZ2Multiply[g1_List, g2_List]:=Mod[{
g1[[1]]*g2[[1]]+g1[[1]]*g2[[2]]+g1[[2]]*g2[[1]],
g1[[1]]*g2[[3]]+g1[[1]]*g2[[4]]+g1[[1]]*g2[[5]]+g1[[1]]*g2[[7]]+g1[[1]]*g2[[8]]+g1[[2]]*g2[[3]]+g1[[2]]*g2[[4]]+g1[[2]]*g2[[7]]+g1[[3]]*g2[[1]]+g1[[3]]*g2[[2]]+g1[[4]]*g2[[1]]+g1[[4]]*g2[[2]]+g1[[5]]*g2[[1]]+g1[[7]]*g2[[1]]+g1[[7]]*g2[[2]]+g1[[8]]*g2[[1]],
g1[[1]]*g2[[3]]+g1[[1]]*g2[[4]]+g1[[1]]*g2[[6]]+g1[[1]]*g2[[7]]+g1[[1]]*g2[[9]]+g1[[2]]*g2[[3]]+g1[[2]]*g2[[4]]+g1[[2]]*g2[[7]]+g1[[3]]*g2[[1]]+g1[[3]]*g2[[2]]+g1[[4]]*g2[[1]]+g1[[4]]*g2[[2]]+g1[[6]]*g2[[1]]+g1[[7]]*g2[[1]]+g1[[7]]*g2[[2]]+g1[[9]]*g2[[1]],
g1[[2]]*g2[[2]],
g1[[2]]*g2[[5]]+g1[[2]]*g2[[8]]+g1[[5]]*g2[[2]]+g1[[8]]*g2[[2]],
g1[[2]]*g2[[6]]+g1[[2]]*g2[[9]]+g1[[6]]*g2[[2]]+g1[[9]]*g2[[2]],
g1[[2]]*g2[[3]]+g1[[2]]*g2[[7]]+g1[[3]]*g2[[2]]+g1[[3]]*g2[[3]]+g1[[3]]*g2[[7]]+g1[[7]]*g2[[2]]+g1[[7]]*g2[[3]],
g1[[2]]*g2[[3]]+g1[[2]]*g2[[4]]+g1[[2]]*g2[[7]]+g1[[3]]*g2[[2]]+g1[[3]]*g2[[4]]+g1[[3]]*g2[[7]]+g1[[4]]*g2[[2]]+g1[[4]]*g2[[3]]+g1[[7]]*g2[[2]]+g1[[7]]*g2[[3]],
g1[[2]]*g2[[4]]+g1[[3]]*g2[[6]]+g1[[4]]*g2[[2]]+g1[[4]]*g2[[4]]+g1[[4]]*g2[[9]]+g1[[6]]*g2[[3]]+g1[[6]]*g2[[7]]+g1[[7]]*g2[[6]]+g1[[9]]*g2[[4]],
g1[[4]]*g2[[6]]+g1[[4]]*g2[[9]]+g1[[6]]*g2[[4]]+g1[[6]]*g2[[7]]+g1[[7]]*g2[[6]]+g1[[9]]*g2[[4]],
g1[[5]]*g2[[5]]+g1[[5]]*g2[[6]]+g1[[6]]*g2[[5]],
g1[[6]]*g2[[6]],
g1[[1]]*g2[[10]]+g1[[10]]*g2[[1]],
g1[[2]]*g2[[10]]+g1[[10]]*g2[[2]],
g1[[3]]*g2[[10]]+g1[[7]]*g2[[7]]+g1[[7]]*g2[[10]]+g1[[10]]*g2[[3]]+g1[[10]]*g2[[7]],
g1[[4]]*g2[[10]]+g1[[7]]*g2[[9]]+g1[[7]]*g2[[10]]+g1[[9]]*g2[[7]]+g1[[10]]*g2[[4]]+g1[[10]]*g2[[7]],
g1[[5]]*g2[[10]]+g1[[8]]*g2[[8]]+g1[[8]]*g2[[9]]+g1[[9]]*g2[[8]]+g1[[10]]*g2[[5]],
g1[[6]]*g2[[10]]+g1[[9]]*g2[[9]]+g1[[10]]*g2[[6]],
g1[[10]]*g2[[10]]
},2]


p4mZ2Multiply1[g1_List,g2_List]:=Mod[p4mZ2Multiply[{g1[[1]],g1[[2]],0,g1[[4]],0,0,g1[[7]],g1[[8]],g1[[9]],0},{0,0,g2[[7]],g2[[7]],0,0,g2[[7]],g2[[8]],g2[[9]],0}]+
p4mZ2Multiply[{0,0,g1[[3]],0,g1[[5]],g1[[6]],0,0,0,g1[[10]]},{g2[[1]],g2[[2]],g2[[3]],g2[[4]],g2[[5]],g2[[6]],0,0,0,g2[[10]]}],2]


p4mZ2Multiply2[g1_List,g2_List]:=Mod[p4mZ2Multiply[{0,0,0,g1[[4]],g1[[5]],g1[[6]],g1[[7]],g1[[8]],g1[[9]],0},{0,0,g2[[7]],0,g2[[8]],g2[[9]],g2[[7]],g2[[8]],g2[[9]],0}]+
p4mZ2Multiply[{g1[[1]],g1[[2]],g1[[3]],g1[[3]],0,0,0,0,g1[[10]],g1[[10]]},{g2[[1]],g2[[2]],g2[[3]],g2[[4]],g2[[5]],g2[[6]],0,0,0,g2[[10]]}],2]


p4mZ2Multiply3[g1_List,g2_List]:=Mod[p4mZ2Multiply[{g1[[1]],g1[[2]],0,g1[[4]],0,g1[[6]],g1[[7]],g1[[8]],g1[[9]],0},{0,0,g2[[7]],g2[[7]],g2[[8]]+g2[[9]],0,g2[[7]],g2[[8]],g2[[9]],0}]+
p4mZ2Multiply[{0,0,g1[[3]],0,g1[[5]],g1[[5]],0,g1[[10]],0,g1[[10]]},{g2[[1]],g2[[2]],g2[[3]],g2[[4]],g2[[5]],g2[[6]],0,0,0,g2[[10]]}],2]


p4mZ2Multiply4[g1_List,g2_List]:=Mod[p4mZ2Multiply[{g1[[1]],g1[[2]],0,g1[[4]],0,g1[[6]],g1[[7]],g1[[8]],g1[[9]],0},{0,0,g2[[7]],0,g2[[9]],g2[[9]],g2[[7]],g2[[8]],g2[[9]],0}]+
p4mZ2Multiply[{0,0,g1[[3]],g1[[3]],g1[[5]],0,0,g1[[10]],g1[[10]],g1[[10]]},{g2[[1]],g2[[2]],g2[[3]],g2[[4]],g2[[5]],g2[[6]],0,0,0,g2[[10]]}],2]


p4mZ2Multiply5[g1_List,g2_List]:=Mod[p4mZ2Multiply[{g1[[1]],g1[[2]],g1[[3]],g1[[4]],0,0,g1[[7]],g1[[8]],g1[[9]],0},{0,0,0,g2[[7]]+g2[[9]],0,0,g2[[7]],g2[[8]],g2[[9]],0}]+
p4mZ2Multiply[{0,0,0,g1[[6]],g1[[5]],g1[[6]],g1[[10]],0,0,g1[[10]]},{g2[[1]],g2[[2]],g2[[3]],g2[[4]],g2[[5]],g2[[6]],0,0,0,g2[[10]]}],2]


p4mZ2Multiply6[g1_List,g2_List]:=Mod[p4mZ2Multiply[{0,g1[[2]],g1[[3]],0,g1[[5]],g1[[6]],g1[[7]],g1[[8]],g1[[9]],0},{0,0,0,g2[[9]],g2[[8]],g2[[9]],g2[[7]],g2[[8]],g2[[9]],0}]+
p4mZ2Multiply[{g1[[1]],g1[[1]],g1[[1]],g1[[1]]+g1[[4]],0,0,g1[[10]],0,g1[[10]],g1[[10]]},{g2[[1]],g2[[2]],g2[[3]],g2[[4]],g2[[5]],g2[[6]],0,0,0,g2[[10]]}],2]


p4mZ2Multiply7[g1_List,g2_List]:=Mod[p4mZ2Multiply[{0,g1[[2]],g1[[3]],g1[[4]],g1[[5]],0,g1[[7]],g1[[8]],g1[[9]],0},{0,0,0,g2[[7]]+g2[[9]],g2[[8]]+g2[[9]],0,g2[[7]],g2[[8]],g2[[9]],0}]+
p4mZ2Multiply[{g1[[1]],0,0,g1[[6]],g1[[6]],g1[[6]],g1[[10]],g1[[10]],0,g1[[10]]},{g2[[1]],g2[[2]],g2[[3]],g2[[4]],g2[[5]],g2[[6]],0,0,0,g2[[10]]}],2]


p4mZ2Multiply8[g1_List,g2_List]:=Mod[p4mZ2Multiply[{g1[[1]],g1[[2]],g1[[3]],0,0,g1[[6]],g1[[7]],g1[[8]],g1[[9]],0},{0,0,0,g2[[9]],g2[[9]],g2[[9]],g2[[7]],g2[[8]],g2[[9]],0}]+
p4mZ2Multiply[{0,0,0,g1[[4]],g1[[4]]+g1[[5]],0,g1[[10]],g1[[10]],g1[[10]],g1[[10]]},{g2[[1]],g2[[2]],g2[[3]],g2[[4]],g2[[5]],g2[[6]],0,0,0,g2[[10]]}],2]


p4mZ2Anomaly0=ConstantArray[0,19];
p4mZ2Anomalya=ConstantArray[0,19];p4mZ2Anomalya[[13]]=1;p4mZ2Anomalya[[14]]=1;p4mZ2Anomalya[[15]]=1;p4mZ2Anomalya[[16]]=1; 
p4mZ2Anomalyb=ConstantArray[0,19];p4mZ2Anomalyb[[13]]=1; 
p4mZ2Anomalyc=ConstantArray[0,19];p4mZ2Anomalyc[[15]]=1;p4mZ2Anomalyc[[16]]=1; 
p4mZ2Anomalyab=Mod[p4mZ2Anomalya+p4mZ2Anomalyb,2];
p4mZ2Anomalyac=Mod[p4mZ2Anomalya+p4mZ2Anomalyc,2];
p4mZ2Anomalybc=Mod[p4mZ2Anomalyb+p4mZ2Anomalyc,2];
p4mZ2Anomalyabc=Mod[p4mZ2Anomalya+p4mZ2Anomalyb+p4mZ2Anomalyc,2];


p4mZ2AnomalyCheck[multiply_, homotopylist_]:=Module[{result, Anomaly, matchinganomaly, i, j, SFCe, SFCm},
result={};Do[AppendTo[result, {}], {i, 1, Length[homotopylist]}];
matchinganomaly = {};
For[i=1,i<=Length[homotopylist],i++, 
If[homotopylist[[i]]=="0", AppendTo[matchinganomaly, p4mZ2Anomaly0];];
If[homotopylist[[i]]=="a", AppendTo[matchinganomaly, p4mZ2Anomalya];];
If[homotopylist[[i]]=="b", AppendTo[matchinganomaly, p4mZ2Anomalyb];];
If[homotopylist[[i]]=="c", AppendTo[matchinganomaly, p4mZ2Anomalyc];];
If[homotopylist[[i]]=="a+b", AppendTo[matchinganomaly, p4mZ2Anomalyab];];
If[homotopylist[[i]]=="a+c", AppendTo[matchinganomaly, p4mZ2Anomalyac];];
If[homotopylist[[i]]=="b+c", AppendTo[matchinganomaly, p4mZ2Anomalybc];];
If[homotopylist[[i]]=="a+b+c", AppendTo[matchinganomaly, p4mZ2Anomalyabc];];];

For[i=0,i<2^10,i++,
For[j=0,j<2^10,j++,
SFCe=PadLeft[IntegerDigits[i,2],10];
SFCm=PadLeft[IntegerDigits[j,2],10];
Anomaly=multiply[SFCe, SFCm];
Do[If[Anomaly==matchinganomaly[[i]], AppendTo[result[[i]], {SFCe, SFCm}];Break[]], {i, 1, Length[homotopylist]}];
]];
result]


p4mZ2Generate[Action_, homotopylist_]:=Module[{result, addList, add, i, j},
If[Action==1, result=p4mZ2AnomalyCheck[p4mZ2Multiply1, homotopylist];];
If[Action==2, result=p4mZ2AnomalyCheck[p4mZ2Multiply2, homotopylist];
For[i=1, i<=Length[homotopylist], i++,
addList = {};
For[j=1, j<=Length[result[[i]]], j++,
If[(result[[i]][[j]][[1]][[1]]==0)&&(result[[i]][[j]][[1]][[2]]==0),
add=result[[i]][[j]];add[[1]][[1]]=2;AppendTo[addList,add];
add=result[[i]][[j]];add[[1]][[2]]=2;AppendTo[addList,add];
add=result[[i]][[j]];add[[1]][[1]]=2;add[[1]][[2]]=2;AppendTo[addList,add];];
If[(result[[i]][[j]][[1]][[1]]==0)&&(result[[i]][[j]][[1]][[2]]==1),
add=result[[i]][[j]];add[[1]][[1]]=2;AppendTo[addList,add];];
If[(result[[i]][[j]][[1]][[1]]==1)&&(result[[i]][[j]][[1]][[2]]==0),
add=result[[i]][[j]];add[[1]][[2]]=2;AppendTo[addList,add];];
If[(result[[i]][[j]][[1]][[1]]==1)&&(result[[i]][[j]][[1]][[2]]==1),
add=result[[i]][[j]];add[[1]][[1]]=3;AppendTo[addList,add];];];
result[[i]] = Join[result[[i]], addList];
];];
If[Action==3, result=p4mZ2AnomalyCheck[p4mZ2Multiply3, homotopylist];];
If[Action==4, result=p4mZ2AnomalyCheck[p4mZ2Multiply4, homotopylist];];
If[Action==5, result=p4mZ2AnomalyCheck[p4mZ2Multiply5, homotopylist];];
If[Action==6, result=p4mZ2AnomalyCheck[p4mZ2Multiply6, homotopylist];
For[i=1, i<=Length[homotopylist], i++,
addList = {};
For[j=1, j<=Length[result[[i]]], j++,
If[result[[i]][[j]][[1]][[1]]==0,add=result[[i]][[j]];add[[1]][[1]]=2;AppendTo[addList,add];]];
result[[i]] = Join[result[[i]], addList];
]];
If[Action==7, result=p4mZ2AnomalyCheck[p4mZ2Multiply7, homotopylist];
For[i=1, i<=Length[homotopylist], i++,
addList = {};
For[j=1, j<=Length[result[[i]]], j++,
If[result[[i]][[j]][[1]][[1]]==0,add=result[[i]][[j]];add[[1]][[1]]=2;AppendTo[addList,add];]];
result[[i]] = Join[result[[i]], addList];
]];
If[Action==8, result=p4mZ2AnomalyCheck[p4mZ2Multiply8, homotopylist];];
result]


p4mZ2CheckSF[Action_, SFCe_, SFCm_]:=Module[{Anomaly, lattice},

If[Action==1, Anomaly=p4mZ2Multiply1[SFCe, SFCm];];
If[Action==2, Anomaly=p4mZ2Multiply2[SFCe, SFCm];];
If[Action==3, Anomaly=p4mZ2Multiply3[SFCe, SFCm];];
If[Action==4, Anomaly=p4mZ2Multiply4[SFCe, SFCm];];
If[Action==5, Anomaly=p4mZ2Multiply5[SFCe, SFCm];];
If[Action==6, Anomaly=p4mZ2Multiply6[SFCe, SFCm];];
If[Action==7, Anomaly=p4mZ2Multiply7[SFCe, SFCm];];
If[Action==8, Anomaly=p4mZ2Multiply8[SFCe, SFCm];];

lattice = Which[Anomaly==p4mZ2Anomaly0, lattice="0", 
				Anomaly==p4mZ2Anomalya, lattice="a",
				Anomaly==p4mZ2Anomalyb, lattice="b",
				Anomaly==p4mZ2Anomalyc, lattice="c",
				Anomaly==p4mZ2Anomalyab, lattice="a+b", 
				Anomaly==p4mZ2Anomalyac, lattice="a+c",
				Anomaly==p4mZ2Anomalybc, lattice="b+c",
				Anomaly==p4mZ2Anomalyabc, lattice="a+b+c",
				True, lattice="empty"];

lattice]
