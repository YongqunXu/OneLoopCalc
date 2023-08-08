If[$FrontEnd===Null,$InputFileName,NotebookFileName[]]//DirectoryName//SetDirectory;
Get["/home/yqx/Program/amflow/diffeq_solver/DESolver.m"];
{masters, table} = Get["reduction"];
{mastersde, variables, diffeq} = Get["diffeq"];
{point, boundary} = Get["boundary"];


sol[n_]:=Module[{tablecoe,de,bc,masterexp,allexp},
SetDefaultOptions[];
SetGlobalOptions["WorkingPre" -> 1812, "ChopPre" -> 20];
SetExpansionOptions["XOrder" -> 3624, "LearnXOrder" -> -1, "TestXOrder" -> 5];
tablecoe = Values[table]/.{variables[[1]] -> eta, eps -> boundary[[n,1]]}//Factor;
de = diffeq[[1]]/.{variables[[1]] -> eta, eps -> boundary[[n,1]]}//Factor;
bc = boundary[[n,2]];
LoadSystem[n, de, bc, point[[2]]];
SolveAsyExp[n];
masterexp = masters/.Thread[mastersde -> AsyExp[n]];
allexp = PlusAsyExp@MapThread[TimesAsyExp, {#, masterexp}]&/@tablecoe;
PickZeroRuleS/@allexp];


LaunchKernels[4];
results = ParallelTable[sol[i], {i, Length[boundary]}, DistributedContexts -> All];
CloseKernels[];


Put[Thread[Keys[table] -> Transpose[results]], "solution"];


Quit[];