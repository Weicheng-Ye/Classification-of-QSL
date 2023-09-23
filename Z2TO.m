(* ::Package:: *)

(* ::Section::Closed:: *)
(*Anomaly Indicator*)


IndicatorZ2T[g_List,Action_List, SF_List,ActionGenerate_, SFGenerate_ ]:=Module[{flag,s,Ind},
flag = ActionGenerate[g,Action];
Ind=0;
If[flag==0,
s=SFGenerate[g,g,Action,SF];
Ind=Mod[s[[1]]*s[[2]],2];
];
Ind];

IndicatorZ2TZ2T[g1_List,g2_List,Action_List, SF_List,ActionGenerate_, SFGenerate_]:=Module[{flag1,flag2,s,t,st,Ind},
flag1= ActionGenerate[g1,Action];
flag2= ActionGenerate[g2,Action];
Ind=0;
If[flag1==0&&flag2==0,
s=SFGenerate[g1,g1,Action,SF];
t=SFGenerate[g2,g2,Action,SF];
st=SFGenerate[g1,g2,Action,SF]+SFGenerate[g2,g1,Action,SF];
Ind=Mod[s[[1]]*t[[2]]+s[[2]]*t[[1]]+st[[1]]*st[[2]],2];];
If[flag1==1&&flag2==0,
t=SFGenerate[g2,g2,Action,SF];
Ind=Mod[t[[1]],2];];
If[flag1==0&&flag2==1,
t=SFGenerate[g1,g1,Action,SF];
Ind=Mod[t[[1]],2];];
If[flag1==1&&flag2==1,
st=SFGenerate[g1,g1,Action,SF]+SFGenerate[g2,g2,Action,SF]+SFGenerate[g1,g2,Action,SF]+SFGenerate[g2,g1,Action,SF];
Ind=Mod[st[[1]],2];];
Ind];

IndicatorSO3[Action_List, SF_List,SFGenerate_]:=Module[{s,Ind},
s=SFGenerate[{0,0,0,0,0,1},{0,0,0,0,0,1},Action,SF];
Ind=Mod[s[[1]]*s[[2]],2];
Ind];

IndicatorZ2[g_List,Action_List, SF_List,ActionGenerate_, SFGenerate_]:=Module[{flag,s,st,Ind},
flag=ActionGenerate[g,Action];
Ind =0;
If[flag==0,
st=SFGenerate[{0,0,0,0,0,1},{0,0,0,0,0,1},Action,SF];
s=SFGenerate[g,g,Action,SF];
Ind=Mod[s[[1]]*st[[2]]+s[[2]]*st[[1]],2];
];
Ind]


(* ::Chapter::Closed:: *)
(*Symmetry: p6m*)


p6mBxy[g1_List, g2_List]:=Which[Mod[g1[[3]],6]==0&&Mod[g1[[4]],2]==0, g1[[2]]*g2[[1]],
Mod[g1[[3]],6]==1&&Mod[g1[[4]],2]==0,g2[[1]]*(g2[[1]]-1)/2-g2[[2]]*g2[[1]]+g1[[2]]*(g2[[1]]-g2[[2]]),
Mod[g1[[3]],6]==2&&Mod[g1[[4]],2]==0,g2[[2]]*(g2[[2]]+1)/2-g2[[1]]-g2[[2]]*(g1[[2]]+g2[[1]]),
Mod[g1[[3]],6]==3&&Mod[g1[[4]],2]==0, -g2[[1]]+g2[[2]]-g1[[2]]*g2[[1]],
Mod[g1[[3]],6]==4&&Mod[g1[[4]],2]==0,  g2[[1]]*(g2[[1]]-1)/2+g2[[2]]-g2[[1]]*g1[[2]]+g2[[2]]*(g1[[2]]-g2[[1]]),
Mod[g1[[3]],6]==5&&Mod[g1[[4]],2]==0, g2[[2]]*(g2[[2]]+1)/2+g2[[2]]*(g1[[2]]-g2[[1]]),
Mod[g1[[3]],6]==0&&Mod[g1[[4]],2]==1, (g1[[2]]+g2[[1]])*g2[[2]],
Mod[g1[[3]],6]==1&&Mod[g1[[4]],2]==1, g2[[2]]*(g2[[2]]-1)/2+g1[[2]]*(-g2[[1]]+g2[[2]]),
Mod[g1[[3]],6]==2&&Mod[g1[[4]],2]==1, g2[[1]]*(g2[[1]]+1)/2-g2[[2]]-g2[[1]]*g1[[2]],
Mod[g1[[3]],6]==3&&Mod[g1[[4]],2]==1, g2[[1]]-g2[[2]]-(g1[[2]]-g2[[1]])*g2[[2]],
Mod[g1[[3]],6]==4&&Mod[g1[[4]],2]==1, g2[[2]]*(g2[[2]]-1)/2+g2[[1]]+g1[[2]]*(g2[[1]]-g2[[2]]),
Mod[g1[[3]],6]==5&&Mod[g1[[4]],2]==1,g2[[1]]*(g2[[1]]+1)/2+g2[[1]]*g1[[2]]];


(* ::Section::Closed:: *)
(*O(3)T*)


p6mO3ActionGenerate[g_List,Action_List]:=Mod[g[[3]]*Action[[1]]+g[[4]]*Action[[2]]+g[[5]]*Action[[3]],2];

p6mO3SFGenerate[g1_List,g2_List,Action_List,SF_List]:=Mod[
Which[Action[[1]]==0&&Action[[2]]==0&&Action[[3]]==0,
p6mBxy[g1,g2]*{SF[[1]][[1]],SF[[2]][[1]]}+g1[[3]]*g2[[3]]*{SF[[1]][[2]],SF[[2]][[2]]}+g1[[3]]*g2[[4]]*{SF[[1]][[3]],SF[[2]][[3]]}+g1[[4]]*g2[[4]]*{SF[[1]][[4]],SF[[2]][[4]]}+g1[[3]]*g2[[5]]*{SF[[1]][[5]],SF[[2]][[5]]}+g1[[4]]*g2[[5]]*{SF[[1]][[6]],SF[[2]][[6]]}+g1[[5]]*g2[[5]]*{SF[[1]][[7]],SF[[2]][[7]]}+g1[[6]]*g2[[6]]*{SF[[1]][[8]],SF[[2]][[8]]},
Action[[3]]==1,
p6mBxy[g1,g2]*{SF[[1]],SF[[1]]}+g1[[3]]*g2[[3]]*{SF[[2]],SF[[2]]}+g1[[3]]*g2[[4]]*{SF[[3]],SF[[3]]}+g1[[4]]*g2[[4]]*{SF[[4]],SF[[4]]}+g1[[6]]*g2[[6]]*{SF[[5]],SF[[5]]},
Action[[1]]==0&&Action[[2]]==1&&Action[[3]]==0,
p6mBxy[g1,g2]*{SF[[1]],SF[[1]]}+g1[[3]]*g2[[3]]*{SF[[2]],SF[[2]]}+g1[[3]]*g2[[5]]*{SF[[3]],SF[[3]]}+g1[[5]]*g2[[5]]*{SF[[4]],SF[[4]]}+g1[[6]]*g2[[6]]*{SF[[5]],SF[[5]]},
Action[[1]]==1&&Action[[3]]==0,
p6mBxy[g1,g2]*{SF[[1]],SF[[1]]}+g1[[4]]*g2[[4]]*{SF[[2]],SF[[2]]}+g1[[4]]*g2[[5]]*{SF[[3]],SF[[3]]}+g1[[5]]*g2[[5]]*{SF[[4]],SF[[4]]}+g1[[6]]*g2[[6]]*{SF[[5]],SF[[5]]}]
,2];


p6mO3Multiply[Action_List, SF_List]:={IndicatorZ2T[{0,0,0,0,1,0},Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate],
IndicatorZ2T[{0,0,0,1,0,0},Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate],
IndicatorZ2T[{0,0,3,0,1,0},Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate],
IndicatorZ2T[{0,0,3,1,0,0},Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate],
IndicatorZ2TZ2T[{0,0,0,0,1,0},{0,0,3,0,1,0},Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate],
IndicatorZ2TZ2T[{0,0,0,0,1,0},{0,0,0,1,0,0},Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate],
IndicatorZ2TZ2T[{0,0,0,1,0,0},{0,0,3,0,1,0},Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate],
IndicatorZ2TZ2T[{0,0,3,0,1,0},{0,0,3,1,0,0},Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate],
IndicatorZ2TZ2T[{0,0,0,1,0,0},{0,0,3,1,0,0},Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate],
IndicatorZ2T[{1,1,3,0,1,0},Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate],
IndicatorZ2TZ2T[{0,0,0,1,0,0},{1,1,3,0,1,0},Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate],
IndicatorZ2TZ2T[{0,0,0,0,1,0},{1,1,3,0,1,0},Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate],
IndicatorZ2TZ2T[{0,0,0,1,0,0},{1,1,3,1,0,0},Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate],
IndicatorZ2T[{0,0,0,0,1,1},Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate],
IndicatorZ2T[{0,0,0,1,0,1},Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate],
IndicatorZ2T[{0,0,3,0,1,1},Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate],
IndicatorZ2T[{0,0,3,1,0,1},Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate],
IndicatorZ2T[{1,1,3,0,1,1},Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate],
IndicatorSO3[Action, SF, p6mO3SFGenerate],
IndicatorZ2[{0,0,3,0,0,0},Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate],
IndicatorZ2[{0,0,0,1,1,0},Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate]}


p6mO3Anomaly0=ConstantArray[0,21];
p6mO3Anomalya=ConstantArray[0,21];p6mO3Anomalya[[3]]=1;p6mO3Anomalya[[5]]=1;p6mO3Anomalya[[20]]=1;
p6mO3Anomalyc=ConstantArray[0,21];p6mO3Anomalyc[[10]]=1;p6mO3Anomalyc[[12]]=1;
p6mO3Anomalyac=Mod[p6mO3Anomalya+p6mO3Anomalyc,2];


p6mO3Generate[Action_,homotopylist_]:=Module[{result,ActionList, Anomaly, matchinganomaly, i, j, SFCe, SFCm},
result={};Do[AppendTo[result, {}], {i, 1, Length[homotopylist]}];
matchinganomaly = {};
For[i=1,i<=Length[homotopylist],i++, 
If[homotopylist[[i]]=="0", AppendTo[matchinganomaly, p6mO3Anomaly0];];
If[homotopylist[[i]]=="a", AppendTo[matchinganomaly, p6mO3Anomalya];];
If[homotopylist[[i]]=="c", AppendTo[matchinganomaly, p6mO3Anomalyc];];
If[homotopylist[[i]]=="a+c", AppendTo[matchinganomaly, p6mO3Anomalyac];];];
ActionList=Which[Action==1,{0,0,0},
(Action>=2)&&(Action<=5),Join[PadLeft[IntegerDigits[Action-2,2],2],{1}],
(Action>=6)&&(Action<=8),Join[PadLeft[IntegerDigits[Action-5,2],2],{0}]];
If[Action==1,
For[i=0,i<2^8,i++,
	For[j=0,j<=i,j++,
SFCe=PadLeft[IntegerDigits[i,2],8];
SFCm=PadLeft[IntegerDigits[j,2],8];
Anomaly=p6mO3Multiply[ActionList,{SFCe,SFCm}];
Do[If[Anomaly==matchinganomaly[[i]], AppendTo[result[[i]], Join[SFCe, SFCm]];Break[]], {i, 1, Length[homotopylist]}];
]]];
If[Action>1,
For[i=0,i<2^5,i++,
SFCe=PadLeft[IntegerDigits[i,2],5];
Anomaly=p6mO3Multiply[ActionList,SFCe];
Do[If[Anomaly==matchinganomaly[[i]], AppendTo[result[[i]], SFCe];Break[]], {i, 1, Length[homotopylist]}];];
];
result]


p6mO3CheckSF[Action_, SF_]:=Module[{Anomaly,ActionList, lattice},
ActionList=Which[Action==1,{0,0,0},
(Action>=2)&&(Action<=5),Join[PadLeft[IntegerDigits[Action-2,2],2],{1}],
(Action>=6)&&(Action<=8),Join[PadLeft[IntegerDigits[Action-5,2],2],{0}]];

Anomaly=If[Action==1,p6mO3Multiply[ActionList,{SF[[1;;8]],SF[[9;;16]]}],p6mO3Multiply[ActionList,SF]];

lattice = Which[Anomaly==p6mO3Anomaly0, lattice="0", 
				Anomaly==p6mO3Anomalya, lattice="a",
				Anomaly==p6mO3Anomalyc, lattice="c",
				Anomaly==p6mO3Anomalyac, lattice="a+c",
				True, lattice="empty"];

lattice]


(* ::Section::Closed:: *)
(*Z2T*)


p6mZ2ActionGenerate[g_List,Action_List]:=Mod[g[[3]]*Action[[1]]+g[[4]]*Action[[2]]+g[[5]]*Action[[3]],2];

p6mZ2SFGenerate[g1_List,g2_List,Action_List,SF_List]:=Mod[
Which[Action[[1]]==0&&Action[[2]]==0&&Action[[3]]==0,
p6mBxy[g1,g2]*{SF[[1]][[1]],SF[[2]][[1]]}+g1[[3]]*g2[[3]]*{SF[[1]][[2]],SF[[2]][[2]]}+g1[[3]]*g2[[4]]*{SF[[1]][[3]],SF[[2]][[3]]}+g1[[4]]*g2[[4]]*{SF[[1]][[4]],SF[[2]][[4]]}+g1[[3]]*g2[[5]]*{SF[[1]][[5]],SF[[2]][[5]]}+g1[[4]]*g2[[5]]*{SF[[1]][[6]],SF[[2]][[6]]}+g1[[5]]*g2[[5]]*{SF[[1]][[7]],SF[[2]][[7]]},
Action[[3]]==1,
p6mBxy[g1,g2]*{SF[[1]],SF[[1]]}+g1[[3]]*g2[[3]]*{SF[[2]],SF[[2]]}+g1[[3]]*g2[[4]]*{SF[[3]],SF[[3]]}+g1[[4]]*g2[[4]]*{SF[[4]],SF[[4]]},
Action[[1]]==0&&Action[[2]]==1&&Action[[3]]==0,
p6mBxy[g1,g2]*{SF[[1]],SF[[1]]}+g1[[3]]*g2[[3]]*{SF[[2]],SF[[2]]}+g1[[3]]*g2[[5]]*{SF[[3]],SF[[3]]}+g1[[5]]*g2[[5]]*{SF[[4]],SF[[4]]},
Action[[1]]==1&&Action[[3]]==0,
p6mBxy[g1,g2]*{SF[[1]],SF[[1]]}+g1[[4]]*g2[[4]]*{SF[[2]],SF[[2]]}+g1[[4]]*g2[[5]]*{SF[[3]],SF[[3]]}+g1[[5]]*g2[[5]]*{SF[[4]],SF[[4]]}]
,2];


p6mZ2Multiply[Action_List, SF_List]:={IndicatorZ2T[{0,0,0,0,1,0},Action, SF, p6mZ2ActionGenerate, p6mZ2SFGenerate],
IndicatorZ2T[{0,0,0,1,0,0},Action, SF, p6mZ2ActionGenerate, p6mZ2SFGenerate],
IndicatorZ2T[{0,0,3,0,1,0},Action, SF, p6mZ2ActionGenerate, p6mZ2SFGenerate],
IndicatorZ2T[{0,0,3,1,0,0},Action, SF, p6mZ2ActionGenerate, p6mZ2SFGenerate],
IndicatorZ2TZ2T[{0,0,0,0,1,0},{0,0,3,0,1,0},Action, SF, p6mZ2ActionGenerate, p6mZ2SFGenerate],
IndicatorZ2TZ2T[{0,0,0,0,1,0},{0,0,0,1,0,0},Action, SF, p6mZ2ActionGenerate, p6mZ2SFGenerate],
IndicatorZ2TZ2T[{0,0,0,1,0,0},{0,0,3,0,1,0},Action, SF, p6mZ2ActionGenerate, p6mZ2SFGenerate],
IndicatorZ2TZ2T[{0,0,3,0,1,0},{0,0,3,1,0,0},Action, SF, p6mZ2ActionGenerate, p6mZ2SFGenerate],
IndicatorZ2TZ2T[{0,0,0,1,0,0},{0,0,3,1,0,0},Action, SF, p6mZ2ActionGenerate, p6mZ2SFGenerate],
IndicatorZ2T[{1,1,3,0,1,0},Action, SF, p6mZ2ActionGenerate, p6mZ2SFGenerate],
IndicatorZ2TZ2T[{0,0,0,1,0,0},{1,1,3,0,1,0},Action, SF, p6mZ2ActionGenerate, p6mZ2SFGenerate],
IndicatorZ2TZ2T[{0,0,0,0,1,0},{1,1,3,0,1,0},Action, SF, p6mZ2ActionGenerate, p6mZ2SFGenerate],
IndicatorZ2TZ2T[{0,0,0,1,0,0},{1,1,3,1,0,0},Action, SF, p6mZ2ActionGenerate, p6mZ2SFGenerate]}


p6mZ2Anomaly0=ConstantArray[0,13];
p6mZ2Anomalya=ConstantArray[0,13];p6mZ2Anomalya[[3]]=1;p6mZ2Anomalya[[5]]=1;
p6mZ2Anomalyc=ConstantArray[0,13];p6mZ2Anomalyc[[10]]=1;p6mZ2Anomalyc[[12]]=1;
p6mZ2Anomalyac=Mod[p6mZ2Anomalya+p6mZ2Anomalyc,2];


p6mZ2Generate[Action_,homotopylist_]:=Module[{result,ActionList, Anomaly, matchinganomaly, i, j, SFCe, SFCm},
result={};Do[AppendTo[result, {}], {i, 1, Length[homotopylist]}];
matchinganomaly = {};
For[i=1,i<=Length[homotopylist],i++, 
If[homotopylist[[i]]=="0", AppendTo[matchinganomaly, p6mZ2Anomaly0];];
If[homotopylist[[i]]=="a", AppendTo[matchinganomaly, p6mZ2Anomalya];];
If[homotopylist[[i]]=="c", AppendTo[matchinganomaly, p6mZ2Anomalyc];];
If[homotopylist[[i]]=="a+c", AppendTo[matchinganomaly, p6mZ2Anomalyac];];];
ActionList=Which[Action==1,{0,0,0},
(Action>=2)&&(Action<=5),Join[PadLeft[IntegerDigits[Action-2,2],2],{1}],
(Action>=6)&&(Action<=8),Join[PadLeft[IntegerDigits[Action-5,2],2],{0}]];
If[Action==1,
For[i=0,i<2^7,i++,
	For[j=0,j<=i,j++,
SFCe=PadLeft[IntegerDigits[i,2],7];
SFCm=PadLeft[IntegerDigits[j,2],7];
Anomaly=p6mZ2Multiply[ActionList,{SFCe,SFCm}];
Do[If[Anomaly==matchinganomaly[[i]], AppendTo[result[[i]], Join[SFCe, SFCm]];Break[]], {i, 1, Length[homotopylist]}];
]]];
If[Action>1,
For[i=0,i<2^4,i++,
SFCe=PadLeft[IntegerDigits[i,2],4];
Anomaly=p6mZ2Multiply[ActionList,SFCe];
Do[If[Anomaly==matchinganomaly[[i]], AppendTo[result[[i]], SFCe];Break[]], {i, 1, Length[homotopylist]}];];
];
result]


p6mZ2CheckSF[Action_, SF_]:=Module[{Anomaly,ActionList, lattice},
ActionList=Which[Action==1,{0,0,0},
(Action>=2)&&(Action<=5),Join[PadLeft[IntegerDigits[Action-2,2],2],{1}],
(Action>=6)&&(Action<=8),Join[PadLeft[IntegerDigits[Action-5,2],2],{0}]];

Anomaly=If[Action==1,p6mZ2Multiply[ActionList,{SF[[1;;7]],SF[[8;;14]]}],p6mZ2Multiply[ActionList,SF]];

lattice = Which[Anomaly==p6mZ2Anomaly0, lattice="0", 
				Anomaly==p6mZ2Anomalya, lattice="a",
				Anomaly==p6mZ2Anomalyc, lattice="c",
				Anomaly==p6mZ2Anomalyac, lattice="a+c",
				True, lattice="empty"];

lattice]


(* ::Chapter::Closed:: *)
(*Symmetry: p4m*)


p4mBxy[g1_List, g2_List]:=Which[Mod[g1[[3]],2]==0,g1[[2]]*g2[[1]],Mod[g1[[3]],2]==1, (g1[[2]]+ g2[[1]])*(g2[[2]])]
p4mBc2[g1_List, g2_List]:=(g1[[3]]+(-1)^(g1[[4]])*g2[[3]]-Mod[g1[[3]]+(-1)^(g1[[4]])* g2[[3]],4])/4


Flip[w_List]:={w[[2]],w[[1]]};

p4maction1wasym1[g1_List, g2_List]:={g1[[1]]*g2[[4]],g1[[2]]*g2[[4]]};
p4maction1wasym2[g1_List,g2_List]:={(Quotient[g1[[3]],2]+Mod[g1[[3]],2]+g1[[3]]*g1[[4]])*g2[[4]],(Quotient[g1[[3]],2]+g1[[4]]+g1[[3]]*g1[[4]])*g2[[4]]};
p4maction1wasym3[g1_List,g2_List]:={(Quotient[g1[[3]],2]+Mod[g1[[3]],2]+g1[[3]]*g1[[4]])*((1-g1[[3]])*g2[[1]]+g1[[3]]*g2[[2]]),
(Quotient[g1[[3]],2]+g1[[4]]+g1[[3]]*g1[[4]])*((1-g1[[3]])*g2[[2]]+g1[[3]]*g2[[1]])};
p4maction1wasym4[g1_List,g2_List]:={g1[[1]]*g2[[5]],g1[[2]]*g2[[5]]};
p4maction1wasym5[g1_List,g2_List]:={(Quotient[g1[[3]],2]+Mod[g1[[3]],2]+g1[[3]]*g1[[4]])*g2[[5]],(Quotient[g1[[3]],2]+g1[[4]]+g1[[3]]*g1[[4]])*g2[[5]]};

p4maction2wasym1[g1_List, g2_List]:={(Quotient[g1[[3]],2])((1-(g1[[3]]+g1[[4]]))*(Quotient[g2[[3]],2])+(g1[[3]]+g1[[4]])*(Quotient[g2[[3]],2]+Mod[g2[[3]],2])),
(Quotient[g1[[3]],2]+Mod[g1[[3]],2])((1-(g1[[3]]+g1[[4]]))*(Quotient[g2[[3]],2]+Mod[g2[[3]],2])+(g1[[3]]+g1[[4]])*(Quotient[g2[[3]],2]))};
p4maction2wasym2[g1_List,g2_List]:={(Quotient[g1[[3]],2])*g2[[5]],(Quotient[g1[[3]],2]+Mod[g1[[3]],2])*g2[[5]]};

p4maction3wasym1[g1_List,g2_List]:=Module[{result,Inv,Trans},
Inv[g_List]:={1/2 (g[[1]]+g[[2]]+Mod[g[[1]]+g[[2]],2](-1)^(Quotient[g[[3]],2]+g[[4]])),(-g[[1]]+g[[2]]-Mod[g[[1]]+g[[2]],2](-1)^(Quotient[g[[3]],2]+Mod[g[[3]],2]+g[[4]]))/2,Mod[g[[3]]-Mod[g[[4]]+g[[1]]+g[[2]],2],4],Mod[g[[4]]+g[[1]]+g[[2]],2]};
Trans[g_List]:=Which[(g[[3]]==0)&&(g[[4]]==0),{g[[2]],g[[1]],0,0},
(g[[3]]==1)&&(g[[4]]==0),{g[[2]]+1,g[[1]],3,0},
(g[[3]]==2)&&(g[[4]]==0),{g[[2]]+1,g[[1]]-1,2,0},
(g[[3]]==3)&&(g[[4]]==0),{g[[2]],g[[1]]-1,1,0},
(g[[3]]==0)&&(g[[4]]==1),{g[[2]],g[[1]]-1,2,1},
(g[[3]]==1)&&(g[[4]]==1),{g[[2]],g[[1]],1,1},
(g[[3]]==2)&&(g[[4]]==1),{g[[2]]+1,g[[1]],0,1},
(g[[3]]==3)&&(g[[4]]==1),{g[[2]]+1,g[[1]]-1,3,1}];
(*Print[Inv[g1],Inv[g2],Bxy[Inv[g1],Inv[g2]]];*)
result = If[Mod[g1[[1]]+g1[[2]],2]==0,{p4mBxy[Inv[g1],Inv[g2]], p4mBxy[Trans[Inv[g1]], Trans[Inv[g2]]]},
{p4mBxy[Inv[g1],Trans[Inv[g2]]], p4mBxy[Trans[Inv[g1]], Inv[g2]]}
];
result];
p4maction3wasym2[g1_List,g2_List]:={(g1[[2]]+(g1[[1]]+g1[[2]])g1[[3]])*((1-(g1[[1]]+g1[[2]]))(g2[[2]]+(g2[[1]]+g2[[2]])g2[[3]])+(g1[[1]]+g1[[2]])(g2[[2]]+(g2[[1]]+g2[[2]])g2[[3]]+g2[[3]])),
(g1[[2]]+(g1[[1]]+g1[[2]])g1[[3]]+g1[[3]])*((1-(g1[[1]]+g1[[2]]))(g2[[2]]+(g2[[1]]+g2[[2]])g2[[3]]+g2[[3]])+(g1[[1]]+g1[[2]])(g2[[2]]+(g2[[1]]+g2[[2]])g2[[3]]))}
p4maction3wasym3[g1_List,g2_List]:={(g1[[2]]+(g1[[1]]+g1[[2]])g1[[3]])*g2[[5]],(g1[[2]]+(g1[[1]]+g1[[2]])g1[[3]]+g1[[3]])*g2[[5]]}

p4maction4wasym1[g1_List,g2_List]:=Module[{result,Inv,Trans},
Inv[g_List]:=Join[Which[(g[[3]]==0)&&(Mod[g[[1]]+g[[2]]+g[[3]],2]==0),{1/2 (g[[1]]+g[[2]]),(-g[[1]]+g[[2]])/2},
(g[[3]]==1)&&(Mod[g[[1]]+g[[2]]+g[[3]],2]==0),{1/2 (g[[1]]+g[[2]]-1),(-g[[1]]+g[[2]]+1)/2},
(g[[3]]==2)&&(Mod[g[[1]]+g[[2]]+g[[3]],2]==0),{1/2 (g[[1]]+g[[2]])-1,(-g[[1]]+g[[2]])/2},
(g[[3]]==3)&&(Mod[g[[1]]+g[[2]]+g[[3]],2]==0),{1/2 (g[[1]]+g[[2]]-1),(-g[[1]]+g[[2]]-1)/2},
(g[[3]]==1)&&(Mod[g[[1]]+g[[2]]+g[[3]],2]==1),{1/2 (g[[1]]+g[[2]])-1,(-g[[1]]+g[[2]])/2},
(g[[3]]==2)&&(Mod[g[[1]]+g[[2]]+g[[3]],2]==1),{1/2 (g[[1]]+g[[2]]-1),(-g[[1]]+g[[2]]-1)/2},
(g[[3]]==3)&&(Mod[g[[1]]+g[[2]]+g[[3]],2]==1),{1/2 (g[[1]]+g[[2]]),(-g[[1]]+g[[2]])/2},
(g[[3]]==0)&&(Mod[g[[1]]+g[[2]]+g[[3]],2]==1),{1/2 (g[[1]]+g[[2]]-1),(-g[[1]]+g[[2]]+1)/2}],{Mod[g[[3]]-Mod[g[[3]]+g[[1]]+g[[2]],2],4],Mod[g[[3]]+g[[1]]+g[[2]],2]}];
Trans[g_List]:=Which[(g[[3]]==0)&&(g[[4]]==0),{g[[2]],g[[1]],0,0},
(g[[3]]==1)&&(g[[4]]==0),{g[[2]]-1,g[[1]],3,0},
(g[[3]]==2)&&(g[[4]]==0),{g[[2]]-1,g[[1]]+1,2,0},
(g[[3]]==3)&&(g[[4]]==0),{g[[2]],g[[1]]+1,1,0},
(g[[3]]==0)&&(g[[4]]==1),{g[[2]],g[[1]]+1,2,1},
(g[[3]]==1)&&(g[[4]]==1),{g[[2]],g[[1]],1,1},
(g[[3]]==2)&&(g[[4]]==1),{g[[2]]-1,g[[1]],0,1},
(g[[3]]==3)&&(g[[4]]==1),{g[[2]]-1,g[[1]]+1,3,1}];
(*Print[Inv[g1],Inv[g2],Bxy[Inv[g1],Inv[g2]]];*)
result = If[Mod[g1[[1]]+g1[[2]]+g1[[3]]+g1[[4]],2]==0,{p4mBxy[Inv[g1],Inv[g2]], p4mBxy[Trans[Inv[g1]], Trans[Inv[g2]]]},
{p4mBxy[Inv[g1],Trans[Inv[g2]]], p4mBxy[Trans[Inv[g1]], Inv[g2]]}
];
result];
p4maction4wasym2[g1_List,g2_List]:={(g1[[2]]+Quotient[g1[[3]],2]+(g1[[1]]+g1[[2]]+g1[[3]])g1[[3]])*((1-(g1[[1]]+g1[[2]]+g1[[3]]+g1[[4]]))(g2[[2]]+Quotient[g2[[3]],2]+(g2[[1]]+g2[[2]]+g2[[3]])g2[[3]])+(g1[[1]]+g1[[2]]+g1[[3]]+g1[[4]])(g2[[2]]+Quotient[g2[[3]],2]+(g2[[1]]+g2[[2]])g2[[3]])),
(g1[[2]]+Quotient[g1[[3]],2]+(g1[[1]]+g1[[2]])g1[[3]])*((1-(g1[[1]]+g1[[2]]+g1[[3]]+g1[[4]]))(g2[[2]]+Quotient[g2[[3]],2]+(g2[[1]]+g2[[2]])g2[[3]])+(g1[[1]]+g1[[2]]+g1[[3]]+g1[[4]])(g2[[2]]+Quotient[g2[[3]],2]+(g2[[1]]+g2[[2]]+g2[[3]])g2[[3]]))};
p4maction4wasym3[g1_List,g2_List]:={(g1[[2]]+Quotient[g1[[3]],2]+(g1[[1]]+g1[[2]]+g1[[3]])g1[[3]])*g2[[5]],(g1[[2]]+Quotient[g1[[3]],2]+(g1[[1]]+g1[[2]])g1[[3]])*g2[[5]]}


(* ::Section::Closed:: *)
(*O(3)T*)


p4mO3ActionGenerate[g_List,Action_List]:=Mod[(g[[1]]+g[[2]])*Action[[1]]+g[[3]]*Action[[2]]+g[[4]]*Action[[3]]+g[[5]]*Action[[4]],2];

p4mO3SFGenerate[g1_List,g2_List,Action_List,SF_List]:=Mod[
Which[Action[[1]]==0&&Action[[2]]==0&&Action[[3]]==0&&Action[[4]]==0,
p4mBxy[g1,g2]*{SF[[1]][[1]],SF[[2]][[1]]}+p4mBc2[g1,g2]*{SF[[1]][[2]],SF[[2]][[2]]}+(g1[[1]]+g1[[2]])*(g2[[1]]+g2[[2]])*{SF[[1]][[3]],SF[[2]][[3]]}+(g1[[1]]+g1[[2]])*g2[[4]]*{SF[[1]][[4]],SF[[2]][[4]]}+g1[[3]]*g2[[3]]*{SF[[1]][[5]],SF[[2]][[5]]}+g1[[4]]*g2[[4]]*{SF[[1]][[6]],SF[[2]][[6]]}+
(g1[[1]]+g1[[2]])*g2[[5]]*{SF[[1]][[7]],SF[[2]][[7]]}+g1[[3]]*g2[[5]]*{SF[[1]][[8]],SF[[2]][[8]]}+g1[[4]]*g2[[5]]*{SF[[1]][[9]],SF[[2]][[9]]}+g1[[5]]*g2[[5]]*{SF[[1]][[10]],SF[[2]][[10]]}+g1[[6]]*g2[[6]]*{SF[[1]][[11]],SF[[2]][[11]]},
Action[[4]]==1,
p4mBxy[g1,g2]*{SF[[1]],SF[[1]]}+p4mBc2[g1,g2]*{SF[[2]],SF[[2]]}+(g1[[1]]+g1[[2]])*(g2[[1]]+g2[[2]])*{SF[[3]],SF[[3]]}+(g1[[1]]+g1[[2]])*g2[[4]]*{SF[[4]],SF[[4]]}+g1[[3]]*g2[[3]]*{SF[[5]],SF[[5]]}+g1[[4]]*g2[[4]]*{SF[[6]],SF[[6]]}+g1[[6]]*g2[[6]]*{SF[[7]],SF[[7]]},
Action[[1]]==0&&Action[[2]]==0&&Action[[3]]==1&&Action[[4]]==0,
p4mBxy[g1,g2]*{SF[[1]],SF[[1]]}+p4mBc2[g1,g2]*{SF[[2]],SF[[2]]}+(g1[[1]]+g1[[2]])*(g2[[1]]+g2[[2]])*{SF[[3]],SF[[3]]}+(g1[[1]]+g1[[2]])*g2[[5]]*{SF[[4]],SF[[4]]}+g1[[3]]*g2[[5]]*{SF[[5]],SF[[5]]}+g1[[5]]*g2[[5]]*{SF[[6]],SF[[6]]}+g1[[6]]*g2[[6]]*{SF[[7]],SF[[7]]},
Action[[1]]==0&&Action[[2]]==1&&Action[[3]]==0&&Action[[4]]==0,
p4mBxy[g1,g2]*{SF[[1]],SF[[1]]}+p4mBc2[g1,g2]*{SF[[2]],SF[[2]]}+g1[[5]]*g2[[5]]*{SF[[3]],SF[[3]]}+g1[[6]]*g2[[6]]*{SF[[4]],SF[[4]]}+
p4maction1wasym1[g1,g2]*SF[[5]]+Flip[p4maction1wasym1[g1,g2]]*SF[[6]]+p4maction1wasym2[g1,g2]*SF[[7]]+Flip[p4maction1wasym2[g1,g2]]*SF[[8]]+p4maction1wasym3[g1,g2]*SF[[9]]+Flip[p4maction1wasym3[g1,g2]]*SF[[10]]+p4maction1wasym4[g1,g2]*SF[[11]]+Flip[p4maction1wasym4[g1,g2]]*SF[[12]]+p4maction1wasym5[g1,g2]*SF[[13]]+Flip[p4maction1wasym5[g1,g2]]*SF[[14]],
Action[[1]]==0&&Action[[2]]==1&&Action[[3]]==1&&Action[[4]]==0,
p4mBxy[g1,g2]*{SF[[1]],SF[[1]]}+p4mBc2[g1,g2]*{SF[[2]],SF[[2]]}+(g1[[1]]+g1[[2]])*(g2[[1]]+g2[[2]])*{SF[[3]],SF[[3]]}+(g1[[1]]+g1[[2]])*g2[[5]]*{SF[[4]],SF[[4]]}+g1[[5]]*g2[[5]]*{SF[[5]],SF[[5]]}+g1[[6]]*g2[[6]]*{SF[[6]],SF[[6]]}+
p4maction2wasym1[g1,g2]*SF[[7]]+Flip[p4maction2wasym1[g1,g2]]*SF[[8]]+p4maction2wasym2[g1,g2]*SF[[9]]+Flip[p4maction2wasym2[g1,g2]]*SF[[10]],
Action[[1]]==1&&Action[[2]]==0&&Action[[3]]==0&&Action[[4]]==0,
p4mBc2[g1,g2]*{SF[[1]],SF[[1]]}+g1[[4]]*g2[[4]]*{SF[[2]],SF[[2]]}+g1[[4]]*g2[[5]]*{SF[[3]],SF[[3]]}+g1[[5]]*g2[[5]]*{SF[[4]],SF[[4]]}+g1[[6]]*g2[[6]]*{SF[[5]],SF[[5]]}+
p4maction3wasym1[g1,g2]*SF[[6]]+Flip[p4maction3wasym1[g1,g2]]*SF[[7]]+p4maction3wasym2[g1,g2]*SF[[8]]+Flip[p4maction3wasym2[g1,g2]]*SF[[9]]+p4maction3wasym3[g1,g2]*SF[[10]]+Flip[p4maction3wasym3[g1,g2]]*SF[[11]],
Action[[1]]==1&&Action[[2]]==0&&Action[[3]]==1&&Action[[4]]==0,
p4mBxy[g1,g2]*{SF[[1]],SF[[1]]}+p4mBc2[g1,g2]*{SF[[2]],SF[[2]]}+g1[[4]]*g2[[4]]*{SF[[3]],SF[[3]]}+g1[[3]]*g2[[5]]*{SF[[4]],SF[[4]]}+g1[[4]]*g2[[5]]*{SF[[5]],SF[[5]]}+g1[[5]]*g2[[5]]*{SF[[6]],SF[[6]]}+g1[[6]]*g2[[6]]*{SF[[7]],SF[[7]]},
Action[[1]]==1&&Action[[2]]==1&&Action[[3]]==0&&Action[[4]]==0,
p4mBxy[g1,g2]*{SF[[1]],SF[[1]]}+p4mBc2[g1,g2]*{SF[[2]],SF[[2]]}+g1[[4]]*g2[[4]]*{SF[[3]],SF[[3]]}+g1[[3]]*g2[[5]]*{SF[[4]],SF[[4]]}+g1[[4]]*g2[[5]]*{SF[[5]],SF[[5]]}+g1[[5]]*g2[[5]]*{SF[[6]],SF[[6]]}+g1[[6]]*g2[[6]]*{SF[[7]],SF[[7]]},
Action[[1]]==1&&Action[[2]]==1&&Action[[3]]==1&&Action[[4]]==0,
p4mBc2[g1,g2]*{SF[[1]],SF[[1]]}+g1[[4]]*g2[[4]]*{SF[[2]],SF[[2]]}+g1[[4]]*g2[[5]]*{SF[[3]],SF[[3]]}+g1[[5]]*g2[[5]]*{SF[[4]],SF[[4]]}+g1[[6]]*g2[[6]]*{SF[[5]],SF[[5]]}+
p4maction4wasym1[g1,g2]*SF[[6]]+Flip[p4maction4wasym1[g1,g2]]*SF[[7]]+p4maction4wasym2[g1,g2]*SF[[8]]+Flip[p4maction4wasym2[g1,g2]]*SF[[9]]+p4maction4wasym3[g1,g2]*SF[[10]]+Flip[p4maction4wasym3[g1,g2]]*SF[[11]]],
2];


p4mO3Multiply[Action_List, SF_List]:={IndicatorZ2T[{0,0,0,0,1,0}, Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate],
IndicatorZ2T[{0,0,0,1,0,0}, Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate],

IndicatorZ2T[{0,0,2,0,1,0}, Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate],
IndicatorZ2T[{0,0,1,1,0,0}, Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate],

IndicatorZ2TZ2T[{0,0,0,0,1,0},{0,0,2,0,1,0}, Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate],
IndicatorZ2TZ2T[{0,0,0,0,1,0},{0,0,0,1,0,0}, Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate],
IndicatorZ2TZ2T[{0,0,1,1,0,0},{0,0,0,0,1,0}, Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate],
IndicatorZ2TZ2T[{0,0,2,0,1,0},{0,0,0,1,0,0}, Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate],
IndicatorZ2TZ2T[{0,0,1,1,0,0},{0,0,2,0,1,0}, Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate],

IndicatorZ2T[{1,0,0,1,0,0}, Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate],
IndicatorZ2T[{1,0,2,0,1,0}, Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate],
IndicatorZ2T[{1,1,2,0,1,0}, Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate],
IndicatorZ2TZ2T[{1,0,0,1,0,0},{0,0,0,0,1,0}, Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate],
IndicatorZ2TZ2T[{0,0,0,0,1,0},{1,0,2,0,1,0}, Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate],
IndicatorZ2TZ2T[{0,0,0,0,1,0},{1,1,2,0,1,0}, Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate],
IndicatorZ2TZ2T[{0,0,0,1,0,0},{0,1,2,0,1,0}, Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate],
IndicatorZ2TZ2T[{0,0,0,1,0,0},{0,1,2,1,0,0}, Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate],
IndicatorZ2TZ2T[{0,0,1,1,0,0},{1,-1,2,0,1,0}, Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate],
IndicatorZ2TZ2T[{1,0,0,1,0,0},{1,1,2,0,1,0}, Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate],

IndicatorSO3[Action, SF, p4mO3SFGenerate],

IndicatorZ2T[{0,0,0,0,1,1}, Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate],
IndicatorZ2T[{0,0,0,1,0,1}, Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate],
IndicatorZ2T[{0,0,2,0,1,1}, Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate],
IndicatorZ2T[{0,0,1,1,0,1}, Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate],
IndicatorZ2T[{1,0,0,1,0,1}, Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate],
IndicatorZ2T[{1,0,2,0,1,1}, Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate],
IndicatorZ2T[{1,1,2,0,1,1}, Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate],
IndicatorZ2[{0,0,1,1,1,0}, Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate],
IndicatorZ2[{0,0,0,1,1,0}, Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate],
IndicatorZ2[{1,0,0,1,1,0}, Action, SF, p4mO3ActionGenerate, p4mO3SFGenerate]}


p4mO3Anomaly0= ConstantArray[0,30];
p4mO3Anomalya = ConstantArray[0,30];p4mO3Anomalya[[3]]=1;p4mO3Anomalya[[5]]=1;
p4mO3Anomalyb = ConstantArray[0, 30];p4mO3Anomalyb[[12]]=1;p4mO3Anomalyb[[15]]=1;
p4mO3Anomalyc=ConstantArray[0, 30];p4mO3Anomalyc[[11]]=1;p4mO3Anomalyc[[14]]=1;
p4mO3Anomalyab = Mod[p4mO3Anomalya+p4mO3Anomalyb,2];
p4mO3Anomalyac=Mod[p4mO3Anomalya+p4mO3Anomalyc,2];
p4mO3Anomalybc=Mod[p4mO3Anomalyb+p4mO3Anomalyc,2];
p4mO3Anomalyabc=Mod[p4mO3Anomalya+p4mO3Anomalyb+p4mO3Anomalyc,2];


p4mO3Generate[Action_,homotopylist_]:=Module[{result,ActionList, Anomaly, matchinganomaly, i, j, SFCe, SFCm, SF3Temp, Convert},
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
ActionList=Which[Action==1,{0,0,0,0},
(Action>=2)&&(Action<=9),Join[PadLeft[IntegerDigits[Action-2,2],3],{1}],
(Action>=10)&&(Action<=16),Join[PadLeft[IntegerDigits[Action-9,2],3],{0}]];
If[Action==1,
For[i=0,i<2^11,i++,
	For[j=0,j<=i,j++,
SFCe=PadLeft[IntegerDigits[i,2],11];
SFCm=PadLeft[IntegerDigits[j,2],11];
Anomaly=p4mO3Multiply[ActionList,{SFCe,SFCm}];
Do[If[Anomaly==matchinganomaly[[i]], AppendTo[result[[i]], Join[SFCe, SFCm]];Break[]], {i, 1, Length[homotopylist]}];
]]];
If[((Action>=2)&&(Action<=10))||(Action==14)||(Action==15),
For[i=0,i<2^7,i++,
SFCe=PadLeft[IntegerDigits[i,2],7];
Anomaly=p4mO3Multiply[ActionList,SFCe];
Do[If[Anomaly==matchinganomaly[[i]], AppendTo[result[[i]], SFCe];Break[]], {i, 1, Length[homotopylist]}];];
];
If[Action==11,
For[i=0,i<2^4*3^5,i++,
SFCe=PadLeft[IntegerDigits[Quotient[i,3^5],2],4];
SF3Temp=PadLeft[IntegerDigits[Mod[i,3^5],3],5];
Convert[j_]:=Which[j==0,{0,0}, j==1,{1,0},j==2,{1,1}];
SFCm = {};
For[j=1,j<=5,j++,SFCm = Join[SFCm,Convert[SF3Temp[[j]]]];];
Anomaly=p4mO3Multiply[ActionList,Join[SFCe, SFCm]];
Do[If[Anomaly==matchinganomaly[[k]], AppendTo[result[[k]], Join[SFCe,SFCm]];Break[]], {k, 1, Length[homotopylist]}];];
];
If[Action==12,
For[i=0,i<2^6*3^2,i++,
SFCe=PadLeft[IntegerDigits[Quotient[i,3^2],2],6];
SF3Temp=PadLeft[IntegerDigits[Mod[i,3^2],3],2];
Convert[i_]:=Which[i==0,{0,0},i==1,{1,0},i==2,{1,1}];
SFCm = {};
For[j=1,j<=2,j++,SFCm = Join[SFCm,Convert[SF3Temp[[j]]]];];
Anomaly=p4mO3Multiply[ActionList,Join[SFCe, SFCm]];
Do[If[Anomaly==matchinganomaly[[i]], AppendTo[result[[i]], Join[SFCe,SFCm]];Break[]], {i, 1, Length[homotopylist]}];];
];
If[(Action==13)||(Action==16),
For[i=0,i<2^5*3^3,i++,
SFCe=PadLeft[IntegerDigits[Quotient[i,3^3],2],5];
SF3Temp=PadLeft[IntegerDigits[Mod[i,3^3],3],3];
Convert[i_]:=Which[i==0,{0,0},i==1,{1,0},i==2,{1,1}];
SFCm = {};
For[j=1,j<=3,j++,SFCm = Join[SFCm,Convert[SF3Temp[[j]]]];];
Anomaly=p4mO3Multiply[ActionList,Join[SFCe, SFCm]];
Do[If[Anomaly==matchinganomaly[[i]], AppendTo[result[[i]], Join[SFCe,SFCm]];Break[]], {i, 1, Length[homotopylist]}];];
];
result]


p4mO3CheckSF[Action_, SF_]:=Module[{Anomaly,ActionList, lattice},
ActionList=Which[Action==1,{0,0,0,0},
(Action>=2)&&(Action<=9),Join[PadLeft[IntegerDigits[Action-2,2],3],{1}],
(Action>=10)&&(Action<=16),Join[PadLeft[IntegerDigits[Action-9,2],3],{0}]];

Anomaly=If[Action==1,p4mO3Multiply[ActionList,{SF[[1;;11]],SF[[12;;22]]}],p4mO3Multiply[ActionList,SF]];

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
(*Z2T*)


p4mZ2ActionGenerate[g_List,Action_List]:=Mod[(g[[1]]+g[[2]])*Action[[1]]+g[[3]]*Action[[2]]+g[[4]]*Action[[3]]+g[[5]]*Action[[4]],2];

p4mZ2SFGenerate[g1_List,g2_List,Action_List,SF_List]:=Mod[
Which[Action[[1]]==0&&Action[[2]]==0&&Action[[3]]==0&&Action[[4]]==0,
p4mBxy[g1,g2]*{SF[[1]][[1]],SF[[2]][[1]]}+p4mBc2[g1,g2]*{SF[[1]][[2]],SF[[2]][[2]]}+(g1[[1]]+g1[[2]])*(g2[[1]]+g2[[2]])*{SF[[1]][[3]],SF[[2]][[3]]}+(g1[[1]]+g1[[2]])*g2[[4]]*{SF[[1]][[4]],SF[[2]][[4]]}+g1[[3]]*g2[[3]]*{SF[[1]][[5]],SF[[2]][[5]]}+g1[[4]]*g2[[4]]*{SF[[1]][[6]],SF[[2]][[6]]}+
(g1[[1]]+g1[[2]])*g2[[5]]*{SF[[1]][[7]],SF[[2]][[7]]}+g1[[3]]*g2[[5]]*{SF[[1]][[8]],SF[[2]][[8]]}+g1[[4]]*g2[[5]]*{SF[[1]][[9]],SF[[2]][[9]]}+g1[[5]]*g2[[5]]*{SF[[1]][[10]],SF[[2]][[10]]},
Action[[4]]==1,
p4mBxy[g1,g2]*{SF[[1]],SF[[1]]}+p4mBc2[g1,g2]*{SF[[2]],SF[[2]]}+(g1[[1]]+g1[[2]])*(g2[[1]]+g2[[2]])*{SF[[3]],SF[[3]]}+(g1[[1]]+g1[[2]])*g2[[4]]*{SF[[4]],SF[[4]]}+g1[[3]]*g2[[3]]*{SF[[5]],SF[[5]]}+g1[[4]]*g2[[4]]*{SF[[6]],SF[[6]]},
Action[[1]]==0&&Action[[2]]==0&&Action[[3]]==1&&Action[[4]]==0,
p4mBxy[g1,g2]*{SF[[1]],SF[[1]]}+p4mBc2[g1,g2]*{SF[[2]],SF[[2]]}+(g1[[1]]+g1[[2]])*(g2[[1]]+g2[[2]])*{SF[[3]],SF[[3]]}+(g1[[1]]+g1[[2]])*g2[[5]]*{SF[[4]],SF[[4]]}+g1[[3]]*g2[[5]]*{SF[[5]],SF[[5]]}+g1[[5]]*g2[[5]]*{SF[[6]],SF[[6]]},
Action[[1]]==0&&Action[[2]]==1&&Action[[3]]==0&&Action[[4]]==0,
p4mBxy[g1,g2]*{SF[[1]],SF[[1]]}+p4mBc2[g1,g2]*{SF[[2]],SF[[2]]}+g1[[5]]*g2[[5]]*{SF[[3]],SF[[3]]}+
p4maction1wasym1[g1,g2]*SF[[4]]+Flip[p4maction1wasym1[g1,g2]]*SF[[5]]+p4maction1wasym2[g1,g2]*SF[[6]]+Flip[p4maction1wasym2[g1,g2]]*SF[[7]]+p4maction1wasym3[g1,g2]*SF[[8]]+Flip[p4maction1wasym3[g1,g2]]*SF[[9]]+p4maction1wasym4[g1,g2]*SF[[10]]+Flip[p4maction1wasym4[g1,g2]]*SF[[11]]+p4maction1wasym5[g1,g2]*SF[[12]]+Flip[p4maction1wasym5[g1,g2]]*SF[[13]],
Action[[1]]==0&&Action[[2]]==1&&Action[[3]]==1&&Action[[4]]==0,
p4mBxy[g1,g2]*{SF[[1]],SF[[1]]}+p4mBc2[g1,g2]*{SF[[2]],SF[[2]]}+(g1[[1]]+g1[[2]])*(g2[[1]]+g2[[2]])*{SF[[3]],SF[[3]]}+(g1[[1]]+g1[[2]])*g2[[5]]*{SF[[4]],SF[[4]]}+g1[[5]]*g2[[5]]*{SF[[5]],SF[[5]]}+
p4maction2wasym1[g1,g2]*SF[[6]]+Flip[p4maction2wasym1[g1,g2]]*SF[[7]]+p4maction2wasym2[g1,g2]*SF[[8]]+Flip[p4maction2wasym2[g1,g2]]*SF[[9]],
Action[[1]]==1&&Action[[2]]==0&&Action[[3]]==0&&Action[[4]]==0,
p4mBc2[g1,g2]*{SF[[1]],SF[[1]]}+g1[[4]]*g2[[4]]*{SF[[2]],SF[[2]]}+g1[[4]]*g2[[5]]*{SF[[3]],SF[[3]]}+g1[[5]]*g2[[5]]*{SF[[4]],SF[[4]]}+
p4maction3wasym1[g1,g2]*SF[[5]]+Flip[p4maction3wasym1[g1,g2]]*SF[[6]]+p4maction3wasym2[g1,g2]*SF[[7]]+Flip[p4maction3wasym2[g1,g2]]*SF[[8]]+p4maction3wasym3[g1,g2]*SF[[9]]+Flip[p4maction3wasym3[g1,g2]]*SF[[10]],
Action[[1]]==1&&Action[[2]]==0&&Action[[3]]==1&&Action[[4]]==0,
p4mBxy[g1,g2]*{SF[[1]],SF[[1]]}+p4mBc2[g1,g2]*{SF[[2]],SF[[2]]}+g1[[4]]*g2[[4]]*{SF[[3]],SF[[3]]}+g1[[3]]*g2[[5]]*{SF[[4]],SF[[4]]}+g1[[4]]*g2[[5]]*{SF[[5]],SF[[5]]}+g1[[5]]*g2[[5]]*{SF[[6]],SF[[6]]},
Action[[1]]==1&&Action[[2]]==1&&Action[[3]]==0&&Action[[4]]==0,
p4mBxy[g1,g2]*{SF[[1]],SF[[1]]}+p4mBc2[g1,g2]*{SF[[2]],SF[[2]]}+g1[[4]]*g2[[4]]*{SF[[3]],SF[[3]]}+g1[[3]]*g2[[5]]*{SF[[4]],SF[[4]]}+g1[[4]]*g2[[5]]*{SF[[5]],SF[[5]]}+g1[[5]]*g2[[5]]*{SF[[6]],SF[[6]]},
Action[[1]]==1&&Action[[2]]==1&&Action[[3]]==1&&Action[[4]]==0,
p4mBc2[g1,g2]*{SF[[1]],SF[[1]]}+g1[[4]]*g2[[4]]*{SF[[2]],SF[[2]]}+g1[[4]]*g2[[5]]*{SF[[3]],SF[[3]]}+g1[[5]]*g2[[5]]*{SF[[4]],SF[[4]]}+
p4maction4wasym1[g1,g2]*SF[[5]]+Flip[p4maction4wasym1[g1,g2]]*SF[[6]]+p4maction4wasym2[g1,g2]*SF[[7]]+Flip[p4maction4wasym2[g1,g2]]*SF[[8]]+p4maction4wasym3[g1,g2]*SF[[9]]+Flip[p4maction4wasym3[g1,g2]]*SF[[10]]],
2];


p4mZ2Multiply[Action_List, SF_List]:={IndicatorZ2T[{0,0,0,0,1}, Action, SF, p4mZ2ActionGenerate, p4mZ2SFGenerate],
IndicatorZ2T[{0,0,0,1,0}, Action, SF, p4mZ2ActionGenerate, p4mZ2SFGenerate],

IndicatorZ2T[{0,0,2,0,1}, Action, SF, p4mZ2ActionGenerate, p4mZ2SFGenerate],
IndicatorZ2T[{0,0,1,1,0}, Action, SF, p4mZ2ActionGenerate, p4mZ2SFGenerate],

IndicatorZ2TZ2T[{0,0,0,0,1},{0,0,2,0,1}, Action, SF, p4mZ2ActionGenerate, p4mZ2SFGenerate],
IndicatorZ2TZ2T[{0,0,0,0,1},{0,0,0,1,0}, Action, SF, p4mZ2ActionGenerate, p4mZ2SFGenerate],
IndicatorZ2TZ2T[{0,0,1,1,0},{0,0,0,0,1}, Action, SF, p4mZ2ActionGenerate, p4mZ2SFGenerate],
IndicatorZ2TZ2T[{0,0,2,0,1},{0,0,0,1,0}, Action, SF, p4mZ2ActionGenerate, p4mZ2SFGenerate],
IndicatorZ2TZ2T[{0,0,1,1,0},{0,0,2,0,1}, Action, SF, p4mZ2ActionGenerate, p4mZ2SFGenerate],

IndicatorZ2T[{1,0,0,1,0}, Action, SF, p4mZ2ActionGenerate, p4mZ2SFGenerate],
IndicatorZ2T[{1,0,2,0,1}, Action, SF, p4mZ2ActionGenerate, p4mZ2SFGenerate],
IndicatorZ2T[{1,1,2,0,1}, Action, SF, p4mZ2ActionGenerate, p4mZ2SFGenerate],
IndicatorZ2TZ2T[{1,0,0,1,0},{0,0,0,0,1}, Action, SF, p4mZ2ActionGenerate, p4mZ2SFGenerate],
IndicatorZ2TZ2T[{0,0,0,0,1},{1,0,2,0,1}, Action, SF, p4mZ2ActionGenerate, p4mZ2SFGenerate],
IndicatorZ2TZ2T[{0,0,0,0,1},{1,1,2,0,1}, Action, SF, p4mZ2ActionGenerate, p4mZ2SFGenerate],
IndicatorZ2TZ2T[{0,0,0,1,0},{0,1,2,0,1}, Action, SF, p4mZ2ActionGenerate, p4mZ2SFGenerate],
IndicatorZ2TZ2T[{0,0,0,1,0},{0,1,2,1,0}, Action, SF, p4mZ2ActionGenerate, p4mZ2SFGenerate],
IndicatorZ2TZ2T[{0,0,1,1,0},{1,-1,2,0,1}, Action, SF, p4mZ2ActionGenerate, p4mZ2SFGenerate],
IndicatorZ2TZ2T[{1,0,0,1,0},{1,1,2,0,1}, Action, SF, p4mZ2ActionGenerate, p4mZ2SFGenerate]}


p4mZ2Anomaly0= ConstantArray[0,19];
p4mZ2Anomalya = ConstantArray[0,19];p4mZ2Anomalya[[3]]=1;p4mZ2Anomalya[[5]]=1;
p4mZ2Anomalyb = ConstantArray[0, 19];p4mZ2Anomalyb[[12]]=1;p4mZ2Anomalyb[[15]]=1;
p4mZ2Anomalyc=ConstantArray[0, 19];p4mZ2Anomalyc[[11]]=1;p4mZ2Anomalyc[[14]]=1;
p4mZ2Anomalyab = Mod[p4mZ2Anomalya+p4mZ2Anomalyb,2];
p4mZ2Anomalyac=Mod[p4mZ2Anomalya+p4mZ2Anomalyc,2];
p4mZ2Anomalybc=Mod[p4mZ2Anomalyb+p4mZ2Anomalyc,2];
p4mZ2Anomalyabc=Mod[p4mZ2Anomalya+p4mZ2Anomalyb+p4mZ2Anomalyc,2];


p4mZ2Generate[Action_,homotopylist_]:=Module[{result,ActionList, Anomaly, matchinganomaly, i, j, SFCe, SFCm, SF3Temp, Convert},
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
ActionList=Which[Action==1,{0,0,0,0},
(Action>=2)&&(Action<=9),Join[PadLeft[IntegerDigits[Action-2,2],3],{1}],
(Action>=10)&&(Action<=16),Join[PadLeft[IntegerDigits[Action-9,2],3],{0}]];
If[Action==1,
For[i=0,i<2^10,i++,
	For[j=0,j<=i,j++,
SFCe=PadLeft[IntegerDigits[i,2],10];
SFCm=PadLeft[IntegerDigits[j,2],10];
Anomaly=p4mZ2Multiply[ActionList,{SFCe,SFCm}];
Do[If[Anomaly==matchinganomaly[[i]], AppendTo[result[[i]], Join[SFCe, SFCm]];Break[]], {i, 1, Length[homotopylist]}];
]]];
If[((Action>=2)&&(Action<=10))||(Action==14)||(Action==15),
For[i=0,i<2^6,i++,
SFCe=PadLeft[IntegerDigits[i,2],6];
Anomaly=p4mZ2Multiply[ActionList,SFCe];
Do[If[Anomaly==matchinganomaly[[i]], AppendTo[result[[i]], SFCe];Break[]], {i, 1, Length[homotopylist]}];];
];
If[Action==11,
For[i=0,i<2^3*3^5,i++,
SFCe=PadLeft[IntegerDigits[Quotient[i,3^5],2],3];
SF3Temp=PadLeft[IntegerDigits[Mod[i,3^5],3],5];
Convert[j_]:=Which[j==0,{0,0}, j==1,{1,0},j==2,{1,1}];
SFCm = {};
For[j=1,j<=5,j++,SFCm = Join[SFCm,Convert[SF3Temp[[j]]]];];
Anomaly=p4mZ2Multiply[ActionList,Join[SFCe, SFCm]];
Do[If[Anomaly==matchinganomaly[[k]], AppendTo[result[[k]], Join[SFCe,SFCm]];Break[]], {k, 1, Length[homotopylist]}];];
];
If[Action==12,
For[i=0,i<2^5*3^2,i++,
SFCe=PadLeft[IntegerDigits[Quotient[i,3^2],2],5];
SF3Temp=PadLeft[IntegerDigits[Mod[i,3^2],3],2];
Convert[i_]:=Which[i==0,{0,0},i==1,{1,0},i==2,{1,1}];
SFCm = {};
For[j=1,j<=2,j++,SFCm = Join[SFCm,Convert[SF3Temp[[j]]]];];
Anomaly=p4mZ2Multiply[ActionList,Join[SFCe, SFCm]];
Do[If[Anomaly==matchinganomaly[[i]], AppendTo[result[[i]], Join[SFCe,SFCm]];Break[]], {i, 1, Length[homotopylist]}];];
];
If[(Action==13)||(Action==16),
For[i=0,i<2^4*3^3,i++,
SFCe=PadLeft[IntegerDigits[Quotient[i,3^3],2],4];
SF3Temp=PadLeft[IntegerDigits[Mod[i,3^3],3],3];
Convert[i_]:=Which[i==0,{0,0},i==1,{1,0},i==2,{1,1}];
SFCm = {};
For[j=1,j<=3,j++,SFCm = Join[SFCm,Convert[SF3Temp[[j]]]];];
Anomaly=p4mZ2Multiply[ActionList,Join[SFCe, SFCm]];
Do[If[Anomaly==matchinganomaly[[i]], AppendTo[result[[i]], Join[SFCe,SFCm]];Break[]], {i, 1, Length[homotopylist]}];];
];
result]


p4mZ2CheckSF[Action_, SF_]:=Module[{Anomaly, ActionList, lattice},
ActionList=Which[Action==1,{0,0,0,0},
(Action>=2)&&(Action<=9),Join[PadLeft[IntegerDigits[Action-2,2],3],{1}],
(Action>=10)&&(Action<=16),Join[PadLeft[IntegerDigits[Action-9,2],3],{0}]];

Anomaly=If[Action==1,p4mZ2Multiply[ActionList,{SF[[1;;10]],SF[[11;;20]]}],p4mZ2Multiply[ActionList,SF]];

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
