If[$FrontEnd===Null,$InputFileName,NotebookFileName[]]//DirectoryName//SetDirectory;
Get["/home/yqx/Program/amflow/diffeq_solver/DESolver.m"];


masters = Get["masters"];
diffeq = Get["diffeq"];
boundary = Get["boundary"];
direction = Get["direction"];
epslist = Get["epslist"];
boundaryMI = Get["boundarymi"];
{regions, powers, pattern} = Get["bpattern"];


pattern = Select[pattern, AnyTrue[Flatten[#[[1]]-boundary[[All,1]]], IntegerQ]&];


sol[n_]:=Module[{epsrule, evaluate, tobcs, bmi, de, bc},
SetDefaultOptions[];
SetGlobalOptions["WorkingPre" -> 312, "ChopPre" -> 20];
SetExpansionOptions["XOrder" -> 624, "ExtraXOrder" -> 20, "LearnXOrder" -> -1, "TestXOrder" -> 5];
SetRunningOptions["RunDirection" -> direction];
evaluate[tab_,list_]:=Map[#.list&,tab/.epsrule,{2}];
tobcs[beh_,tab_]:=MapThread[Thread[#1-Range[0,Length@#2-1]->#2]& ,{beh/.epsrule,tab}];
epsrule = {eps -> epslist[[n]]};
bmi = Map[N[#, $MinPrecision]&, Values[boundaryMI][[All,All,n]], {2}];
de = Together[diffeq/.epsrule];
bc = MapThread[tobcs[#1, evaluate[#2, #3]]&, {boundary[[All,1]], boundary[[All,-1]], bmi}];
bc = Join@@@Transpose[bc];
bc = MapThread[Join[#1,#2]&, {bc, Transpose[Thread/@Thread[(pattern/.epsrule) -> 0]]}];
AMFlow[de, bc]];


LaunchKernels[4];
results = ParallelTable[sol[i], {i, Length[epslist]}, DistributedContexts -> All];
CloseKernels[];


Put[Thread[masters -> Transpose[results]], "solution"];


Quit[];