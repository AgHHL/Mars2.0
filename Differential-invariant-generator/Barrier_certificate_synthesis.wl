Clear["Global`*"];
Clear[Subscript];
If[MatchQ[$FrontEndSession, _FrontEndObject],
 SetOptions[$FrontEndSession, PrintingStyleEnvironment -> "Working"]];


$RunLogLevel = "INFO"; 
$CurrentCaseId = Missing["NotSet"];
$LogLevelRank = <|"ERROR" -> 1, "WARN" -> 2, "INFO" -> 3, "DEBUG" -> 4|>;

formatLogMessage[msg_] := If[StringQ[msg], msg, ToString[msg, InputForm]];
logEnabledQ[level_String] := 
 Lookup[$LogLevelRank, level, 99] <= Lookup[$LogLevelRank, $RunLogLevel, 3];
logMessage[level_String, msg_] := 
 If[logEnabledQ[level], 
  Print["[", level, "] ", 
   If[IntegerQ[$CurrentCaseId], "case " <> ToString[$CurrentCaseId] <> ": ",
     ""], formatLogMessage[msg]]];
logInfo[msg_] := logMessage["INFO", msg];
logWarn[msg_] := logMessage["WARN", msg];
logError[msg_] := logMessage["ERROR", msg];
logDebug[msg_] := logMessage["DEBUG", msg];

zeroConstraintQ[expr_] := 
 TrueQ[expr === 0 || expr === 0. || (NumericQ[expr] && Chop[N[expr]] == 0)];
dropTrivialZeroConstraints[data_] := 
 Module[{cleanOne},
  cleanOne[list_] := 
   DeleteCases[Flatten[list, Infinity], 
    x_ /; x === {} || zeroConstraintQ[x]];
  If[ListQ[data] && data =!= {} && AllTrue[data, ListQ], cleanOne /@ data,
    cleanOne[{data}]]
  ];

$SDPPrimaryOptions = {PerformanceGoal -> "Quality", MaxIterations -> 300};
$SDPFallbackOptions = {PerformanceGoal -> "Quality", MaxIterations -> 1200};
$EnableVectorPositiveCoff = False;
$SDPWarnOnFailure = True;
$LastSDPStatus = "idle";
$SDPCallTimeLimit = 300;
$MethodCallTimeLimit = 600;
$VectorMethodCallTimeLimit = 1200;
$SetupCallTimeLimit = 900;
main[varSet_, flowVec1_, domineq_, domeq_, initialineq_, initialeq_, 
  unsafeineq_, unsafeeq_, barrierDegree_, polyAddDegree_, paraRange_, 
  LieOrder_, \[Epsilon]I_, \[Epsilon]U_, \[Epsilon]L_, \[Epsilon]DC_, \[Epsilon]AD_, \[Epsilon]Vector_, \[Delta]_, seed_, 
  verbose_ : True, bcTempDefault_ : Automatic] := 
 Module[{flowVec, barrierTempDegree, number, time, polyTargetDegree, sosdegree, polydegree, rank, bcTemp, LieSequence, LieConstraints, sosSet, sosConstraint, cMatrix, cMatrixSet, coff, bcCoff, bcTempCoff, bcCoffMax, polyCoff, sigmaCoff, \[Sigma]I, \[Sigma]U, \[Sigma]W, basis, degree, verifiedInitial, verifiedUnsafe, verifiedLie, i, j, n, optimum, bcCandidate, dcRound, dcVerbose, DCverbose, adRound, adVerbose, vectorNum, positiveCoff, exverbose, ansDegree, timebound, cMatrixSetSet, initialComponents, unsafeComponents, comp, ineqComp, eqComp, sigmaIComp, sigmaUComp, setupTimeoutQ, setupStartTime},
  
  optimum = {};
  flowVec = N[flowVec1];
  ansDegree = {0, 0, 0};
  timebound = 3000;
  time = TimeUsed[];
  
  
  cMatrixSetSet = {};
  bcCoff = {};
  sigmaCoff = {};
  polyCoff = {};
  For[barrierTempDegree = 1, barrierTempDegree <= barrierDegree, 
   barrierTempDegree++,
   
   If[bcTempDefault === Automatic, 
    bcTemp = polyTemp[varSet, a, barrierTempDegree], 
    bcTemp = bcTempDefault; 
    barrierTempDegree = polyDegree[bcTemp, varSet]];
   logDebug["Template BC: " <> ToString[bcTemp, InputForm]];
   
   
   LieSequence = LieDerivatives[varSet, flowVec, bcTemp, LieOrder];
   If[verbose, logDebug["Lie sequence: " <> ToString[LieSequence, InputForm]]];
   
   sosSet = {};
   
   
   initialComponents = normalizeComponents[initialineq, initialeq];
   unsafeComponents = normalizeComponents[unsafeineq, unsafeeq];
   \[Sigma]I = {}; \[Sigma]U = {};
   For[comp = 1, comp <= Length[initialComponents], comp++,
    ineqComp = Flatten[initialComponents[[comp, 1]], Infinity]; 
    eqComp = Flatten[initialComponents[[comp, 2]], Infinity];
    ineqComp = Map[If[ListQ[#], First@Flatten[#], #] &, ineqComp];
    eqComp = Map[If[ListQ[#], First@Flatten[#], #] &, eqComp];
    If[Length[ineqComp] == 0 && Length[eqComp] == 0, Continue[]];
    polyTargetDegree = degreeDecision[barrierTempDegree, polyAddDegree, ineqComp, eqComp, varSet];
    If[Length[polyTargetDegree] == 0, 
     logError[
      "Initial-degree setup failed at degree " <> 
       ToString[barrierTempDegree] <> "."];
     Return[];];
    sosdegree = Table[polyTargetDegree[[i]], {i, 1, Length[ineqComp]}];
    polydegree = Table[polyTargetDegree[[Length[ineqComp] + i]], {i, 1, Length[eqComp]}];
    sosdegree = Flatten[sosdegree];
    polydegree = Flatten[polydegree];
    sigmaIComp = Table[polyTemp[varSet, identifier[{r, comp, i}], sosdegree[[i]]], {i, 1, Length[ineqComp]}];
    \[Sigma]I = Join[\[Sigma]I, sigmaIComp];
    If[Length[ineqComp] > 0 || Length[eqComp] > 0,
     AppendTo[sosSet, -bcTemp - Sum[sigmaIComp[[i]]*ineqComp[[i]], {i, 1, Length[ineqComp]}] + Sum[polyTemp[varSet, identifier[{s, comp, i}], polydegree[[i]]]*eqComp[[i]], {i, 1, Length[eqComp]}] - \[Epsilon]I];
     logDebug["Initial component " <> ToString[comp] <> 
       ": sosdegree=" <> ToString[sosdegree, InputForm] <> 
       ", polydegree=" <> ToString[polydegree, InputForm] <> 
       ", totaldegree=" <> ToString[polyDegree[sosSet[[-1]], varSet]]];];
    ];
   
   For[comp = 1, comp <= Length[unsafeComponents], comp++,
    ineqComp = Flatten[unsafeComponents[[comp, 1]], Infinity]; 
    eqComp = Flatten[unsafeComponents[[comp, 2]], Infinity];
    ineqComp = Map[If[ListQ[#], First@Flatten[#], #] &, ineqComp];
    eqComp = Map[If[ListQ[#], First@Flatten[#], #] &, eqComp];
    If[Length[ineqComp] == 0 && Length[eqComp] == 0, Continue[]];
    polyTargetDegree = degreeDecision[barrierTempDegree, polyAddDegree, ineqComp, eqComp, varSet];
    If[Length[polyTargetDegree] == 0, 
     logError[
      "Unsafe-degree setup failed at degree " <> 
       ToString[barrierTempDegree] <> "."];
     Return[];];
    sosdegree = Table[polyTargetDegree[[i]], {i, 1, Length[ineqComp]}];
    polydegree = Table[polyTargetDegree[[Length[ineqComp] + i]], {i, 1, Length[eqComp]}];
    sosdegree = Flatten[sosdegree];
    polydegree = Flatten[polydegree];
    sigmaUComp = Table[polyTemp[varSet, identifier[{t, comp, i}], sosdegree[[i]]], {i, 1, Length[ineqComp]}];
    \[Sigma]U = Join[\[Sigma]U, sigmaUComp];
    If[Length[ineqComp] > 0 || Length[eqComp] > 0,
     AppendTo[sosSet, bcTemp - Sum[sigmaUComp[[i]]*ineqComp[[i]], {i, 1, Length[ineqComp]}] + Sum[polyTemp[varSet, identifier[{u, comp, i}], polydegree[[i]]]*eqComp[[i]], {i, 1, Length[eqComp]}] - \[Epsilon]U];
     logDebug["Unsafe component " <> ToString[comp] <> 
       ": sosdegree=" <> ToString[sosdegree, InputForm] <> 
       ", polydegree=" <> ToString[polydegree, InputForm] <> 
       ", totaldegree=" <> ToString[polyDegree[sosSet[[-1]], varSet]]];];
    ];
   
   \[Sigma]W = {};
   For[i = 1, i <= LieOrder, i++,
    polyTargetDegree = 
     degreeDecision[polyDegree[LieSequence[[i + 1]], varSet], 0, 
      domineq, Join[domeq, Table[LieSequence[[j]], {j, 1, i}]], 
      varSet];
    
    If[Length[polyTargetDegree] == 0, 
     logError[
      "Lie-degree setup failed at degree " <> 
       ToString[barrierTempDegree] <> "."];
     Return[];];
    sosdegree = Table[polyTargetDegree[[j]], {j, 1, Length[domineq]}];
    polydegree = Table[polyTargetDegree[[Length[domineq] + j]], {j, 1, Length[domeq] + i}];
    sosdegree = Flatten[sosdegree];
    polydegree = Flatten[polydegree];
    
    \[Sigma]W = Join[\[Sigma]W, Table[polyTemp[varSet, identifier[{w, i, j}], sosdegree[[j]]], {j, 1, Length[domineq]}]];
    LieConstraints = -LieSequence[[i + 1]] + 
      Sum[polyTemp[varSet, identifier[{v, i, j}], 
         polydegree[[Length[domeq] + j + 1]]]*
        LieSequence[[j + 1]], {j, 0, i - 1}] - 
      Sum[\[Sigma]W[[j]]*domineq[[j]], {j, 1, Length[domineq]}] + 
      Sum[polyTemp[varSet, identifier[{y, i, j}], polydegree[[j]]]*
        domeq[[j]], {j, 1, Length[domeq]}] - \[Epsilon]L;
    
    AppendTo[sosSet, LieConstraints];
    logDebug["Lie constraint: sosdegree=" <> 
      ToString[sosdegree, InputForm] <> ", polydegree=" <> 
      ToString[polydegree, InputForm] <> ", totaldegree=" <> 
      ToString[polyDegree[sosSet[[-1]], varSet]]];
    ];
   sosSet = 
    Map[Collect[#, varSet, Simplify] &, 
     Join[\[Sigma]I, \[Sigma]U, \[Sigma]W, sosSet]];
   If[verbose, Print["SOS constraints:\n", sosSet]];
   
   
   cMatrixSet = {};
   setupTimeoutQ = False;
   setupStartTime = TimeUsed[];
   For[n = 1, n <= Length[sosSet], n++,
    sosConstraint = sosSet[[n]];
    
    degree = Ceiling[polyDegreeMax[sosConstraint, varSet]/2];
    basis = 
     monomList[varSet, degree];
    cMatrix = coefficientMatrix[varSet, basis, sosConstraint];
    If[verbose, 
     Print[n, "th constraint with basis=", basis, " of degree=", 
      polyDegree[sosConstraint, varSet], 
      ":\nF(a,s)=", -cMatrix // MatrixForm]];
    
    cMatrix = -cMatrix + \[Lambda]*IdentityMatrix[Length[cMatrix]];
    If[n == 1, coff = Variables[cMatrix], 
     coff = DeleteDuplicates[Join[coff, Variables[cMatrix]]]];
    AppendTo[cMatrixSet, cMatrix];
    If[TimeUsed[] - setupStartTime > $SetupCallTimeLimit, 
     setupTimeoutQ = True;
     If[TrueQ[$SDPWarnOnFailure], 
      logWarn[
       "Setup time budget exceeded at degree " <> 
        ToString[barrierTempDegree] <> ", constraint " <> ToString[n] <> 
        ". Skipping this degree."]];
     Break[]];
    ];
   If[TrueQ[setupTimeoutQ], 
    AppendTo[cMatrixSetSet, $Failed];
    AppendTo[bcCoff, {}];
    AppendTo[sigmaCoff, {}];
    AppendTo[polyCoff, {}];
    Continue[]];
   AppendTo[cMatrixSetSet, cMatrixSet];
   
   
   
   AppendTo[bcCoff, Cases[coff, Subscript[a, _]]];
   
  AppendTo[sigmaCoff, 
   DeleteDuplicates[Flatten[Join[{\[Lambda]}, 
     Join @@ Table[
       Cases[coff, 
        Subscript[
         ToExpression[StringJoin[ToString /@ {r, comp, i}]], 
         Row[_]]], {comp, 1, Length[initialComponents]}, {i, 1, 
        Length[initialComponents[[comp, 1]]]}], 
     Join @@ Table[
       Cases[coff, 
        Subscript[
         ToExpression[StringJoin[ToString /@ {s, comp, i}]], 
         Row[_]]], {comp, 1, Length[initialComponents]}, {i, 1, 
        Length[initialComponents[[comp, 2]]]}], 
     Join @@ Table[
       Cases[coff, 
        Subscript[
         ToExpression[StringJoin[ToString /@ {t, comp, i}]], 
         Row[_]]], {comp, 1, Length[unsafeComponents]}, {i, 1, 
        Length[unsafeComponents[[comp, 1]]]}], 
     Join @@ Table[
       Cases[coff, 
        Subscript[
         ToExpression[StringJoin[ToString /@ {u, comp, i}]], 
         Row[_]]], {comp, 1, Length[unsafeComponents]}, {i, 1, 
        Length[unsafeComponents[[comp, 2]]]}], 
     Join @@ Join @@ 
       Table[Cases[coff, 
         Subscript[ToExpression[StringJoin[ToString /@ {w, i, j}]], 
          Row[_]]], {i, 1, LieOrder}, {j, 1, Length[domineq]}], 
     Join @@ Join @@ 
       Table[Cases[coff, 
         Subscript[ToExpression[StringJoin[ToString /@ {y, i, j}]], 
          Row[_]]], {i, 1, LieOrder}, {j, 1, Length[domeq]}]]]]];
   
   If[verbose, Print["sigmaCoff=", sigmaCoff[[-1]]]];
   AppendTo[polyCoff, Complement[coff, bcCoff[[-1]], sigmaCoff[[-1]]]];
   If[verbose, Print["polyCoff=", polyCoff[[-1]]]];
   ];
  
  
  
  
  
  For[barrierTempDegree = 1, 
   barrierTempDegree <= barrierDegree && ansDegree[[1]] == 0, 
   barrierTempDegree++,
   If[bcTempDefault === Automatic, 
    bcTemp = polyTemp[varSet, a, barrierTempDegree], 
    bcTemp = bcTempDefault; 
    barrierTempDegree = polyDegree[bcTemp, varSet]];
   If[verbose, Print["ExponentialCon & AD: Template BC=", bcTemp]];
   
   LieSequence = LieDerivatives[varSet, flowVec, bcTemp, LieOrder];
   If[verbose, Print["Lie sequence: \n", LieSequence]];
   If[cMatrixSetSet[[barrierTempDegree]] === $Failed, 
    If[TrueQ[$SDPWarnOnFailure], 
     logWarn[
      "Skipping degree " <> ToString[barrierTempDegree] <> 
       " because setup stage timed out."]]; Continue[]];
   
   
   If[ansDegree[[1]] == 0,
    logInfo[
     "Degree " <> ToString[barrierTempDegree] <> 
      ": trying ExponentialCon."];
    exverbose = False;
    optimum = 
     ExponentialCon[varSet, flowVec, LieOrder, bcTemp, rank, 
      initialineq, initialeq, unsafeineq, unsafeeq, domineq, domeq, 
      paraRange, LieSequence, cMatrixSetSet[[barrierTempDegree]], 
      polyAddDegree, \[Epsilon]L, exverbose];
    If[optimum, 
     ansDegree = {barrierTempDegree, TimeUsed[] - time, 1};
     logInfo[
      "Solved by ExponentialCon at degree " <> 
       ToString[barrierTempDegree] <> "."]];
    If[verbose, Print["\n"]];
    
    If[TimeUsed[] - time > timebound && ansDegree[[1]] == 0, 
     ansDegree[[1]] = -1];
    ];
   
   number = 0;
   While[number < 5 && ansDegree[[1]] == 0, number++;
    If[number == 1, 
     logInfo["Degree " <> ToString[barrierTempDegree] <> ": trying AD."]];
    
    SeedRandom[number + seed];
    If[ansDegree[[1]] == 0,
     adRound = 20;
     adVerbose = False;
     positiveCoff = {};
     optimum = 
      TimeConstrained[
       AD[cMatrixSetSet[[barrierTempDegree]], 
        bcCoff[[barrierTempDegree]], positiveCoff, 
        sigmaCoff[[barrierTempDegree]], 
        polyCoff[[barrierTempDegree]], 
        paraRange, \[Epsilon]AD, adRound, adVerbose], 
       $MethodCallTimeLimit, $Failed];
     If[optimum === $Failed, 
      If[TrueQ[$SDPWarnOnFailure], 
       logDebug[
        Switch[$LastSDPStatus, "timeout", 
         "AD step timed out. Skipping current seed.", "nonconvex", 
         "AD step failed: non-convex SDP subproblem (ctnc). Skipping current seed.", 
         "partial_success", 
         "AD step failed after partial-success SDP return. Skipping current seed.", 
         "bad_return", 
         "AD step failed: unexpected SDP return format. Skipping current seed.", 
         "unevaluated", 
         "AD step failed: SDP stayed unevaluated (likely symbolic/non-numeric constraints). Skipping current seed.", 
         "solver_error", 
         "AD step failed: solver error. Skipping current seed.", _, 
         "AD step failed. Skipping current seed."]]]; Continue[]];
     bcCandidate = bcTemp /. optimum;
     If[verbose, 
      Print["AD: Barrier certificate candidate:", bcCandidate]];
     If[LieOrder > 1,
      bcCandidate = bcCandidate /. x_ /; Abs[x] <= 10^-5 -> 0;
      LieSequence = 
       LieDerivatives[varSet, flowVec, bcCandidate, LieOrder];
      ];
    bcCoffMax = 
     safeCoeffScale[bcCoff[[barrierTempDegree]] /. optimum];
     bcTempCoff = ((bcCoff[[barrierTempDegree]] /. optimum)/
         bcCoffMax) /. x_ /; Abs[x] <= 10^-5 -> 0;
     bcTempCoff = bcTempCoff*bcCoffMax;
     bcCandidate = 
      bcTemp /. (Thread[bcCoff[[barrierTempDegree]] -> bcTempCoff]);
     If[verbose, Print["After estimating, bcCandidate=", bcCandidate]];
     {verifiedLie, verifiedUnsafe, verifiedInitial} = 
      Vertification[varSet, LieOrder, rank, flowVec, initialineq, 
       initialeq, unsafeineq, unsafeeq, bcCandidate, domineq, domeq, 
       optimum, adVerbose];
     If[verifiedLie && verifiedUnsafe && verifiedInitial, 
      If[verbose, Print["AD-verification: True!"]]; 
      ansDegree = {barrierTempDegree, TimeUsed[] - time, 2};
      logInfo["Solved by AD at degree " <> ToString[barrierTempDegree] <> "."], 
      If[verbose, Print["AD-verification: False!"]]];
     
     If[TimeUsed[] - time > timebound && ansDegree[[1]] == 0, 
      ansDegree[[1]] = -1];
     ];
    ];
   ];
  
  
  
   For[barrierTempDegree = 1, 
    barrierTempDegree <= barrierDegree && ansDegree[[1]] == 0, 
    barrierTempDegree++,
    If[bcTempDefault === Automatic, 
     bcTemp = polyTemp[varSet, a, barrierTempDegree], 
     bcTemp = bcTempDefault; 
     barrierTempDegree = polyDegree[bcTemp, varSet]];
    If[verbose, Print["vector-AD: Template BC=", bcTemp]];
    
    LieSequence = LieDerivatives[varSet, flowVec, bcTemp, LieOrder];
    If[verbose, Print["Lie sequence: \n", LieSequence]];
    If[cMatrixSetSet[[barrierTempDegree]] === $Failed, 
     If[TrueQ[$SDPWarnOnFailure], 
      logWarn[
       "Skipping degree " <> ToString[barrierTempDegree] <> 
        " because setup stage timed out."]]; Continue[]];
    logInfo[
     "Degree " <> ToString[barrierTempDegree] <> ": trying Vector-AD."];
    vectorNum = 2;
    optimum = 
     TimeConstrained[
      VectorBC[varSet, flowVec, bcTemp, LieOrder, rank, initialineq, 
       initialeq, unsafeineq, unsafeeq, domineq, domeq, paraRange, 
       polyAddDegree, LieSequence, \[Epsilon]I, \[Epsilon]U, \[Epsilon]L,
        vectorNum, \[Epsilon]Vector, \[Delta], seed, verbose, 1], 
      $VectorMethodCallTimeLimit, $Failed];
    If[optimum === $Failed, 
     If[TrueQ[$SDPWarnOnFailure], 
      logWarn["VectorBC step timed out at this degree."]]; 
     optimum = False];
    If[optimum, 
     ansDegree = {barrierTempDegree, TimeUsed[] - time, 3};
     logInfo[
      "Solved by Vector-AD at degree " <> ToString[barrierTempDegree] <> 
       "."]];
    If[verbose, Print["\n"]];
    If[TimeUsed[] - time > timebound && ansDegree[[1]] == 0, 
     ansDegree[[1]] = -1];
    ];
  
  
  For[barrierTempDegree = 1, 
   barrierTempDegree <= (barrierDegree - 3) && ansDegree[[1]] == 0, 
   barrierTempDegree++,
   If[bcTempDefault === Automatic, 
    bcTemp = polyTemp[varSet, a, barrierTempDegree], 
    bcTemp = bcTempDefault; 
    barrierTempDegree = polyDegree[bcTemp, varSet]];
   If[verbose, Print["DC: Template BC=", bcTemp]];
   
   LieSequence = LieDerivatives[varSet, flowVec, bcTemp, LieOrder];
   If[verbose, Print["Lie sequence: \n", LieSequence]];
   If[cMatrixSetSet[[barrierTempDegree]] === $Failed, 
    If[TrueQ[$SDPWarnOnFailure], 
     logWarn[
      "Skipping degree " <> ToString[barrierTempDegree] <> 
       " because setup stage timed out."]]; Continue[]];
   
   
   number = 0;
   While[number < 5 && ansDegree[[1]] == 0, number++;
    If[number == 1, 
     logInfo["Degree " <> ToString[barrierTempDegree] <> ": trying DC."]];
    
    SeedRandom[number + seed];
    If[ansDegree[[1]] == 0,
     dcRound = 20;
     dcVerbose = False;
     positiveCoff = {};
     optimum = 
      TimeConstrained[
       DC[varSet, flowVec, rank, domineq, domeq, initialineq, 
        initialeq, unsafeineq, unsafeeq, paraRange, LieOrder, 
        \[Epsilon]DC, \[Delta], bcTemp, 
        cMatrixSetSet[[barrierTempDegree]], positiveCoff, 
        sigmaCoff[[barrierTempDegree]], 
        polyCoff[[barrierTempDegree]], 
        dcRound, dcVerbose, Automatic], $MethodCallTimeLimit, $Failed];
     If[optimum === $Failed, 
      If[TrueQ[$SDPWarnOnFailure], 
       logDebug[
        Switch[$LastSDPStatus, "timeout", 
         "DC step timed out. Skipping current seed.", "nonconvex", 
         "DC step failed: non-convex SDP subproblem (ctnc). Skipping current seed.", 
         "partial_success", 
         "DC step failed after partial-success SDP return. Skipping current seed.", 
         "bad_return", 
         "DC step failed: unexpected SDP return format. Skipping current seed.", 
         "unevaluated", 
         "DC step failed: SDP stayed unevaluated (likely symbolic/non-numeric constraints). Skipping current seed.", 
         "solver_error", 
         "DC step failed: solver error. Skipping current seed.", _, 
         "DC step failed. Skipping current seed."]]]; Continue[]];
     bcCandidate = bcTemp /. optimum;
     If[LieOrder > 1,
      bcCandidate = bcCandidate /. x_ /; Abs[x] <= 10^-5 -> 0;
      LieSequence = 
       LieDerivatives[varSet, flowVec, bcCandidate, LieOrder];
      ];
    bcCoffMax = 
     safeCoeffScale[bcCoff[[barrierTempDegree]] /. optimum];
     bcTempCoff = ((bcCoff[[barrierTempDegree]] /. optimum)/
         bcCoffMax) /. x_ /; Abs[x] <= 10^-5 -> 0;
     bcTempCoff = bcTempCoff*bcCoffMax;
     bcCandidate = 
      bcTemp /. (Thread[bcCoff[[barrierTempDegree]] -> bcTempCoff]);
     If[verbose, Print["After estimating, bcCandidate=", bcCandidate]];
     If[verbose, 
      Print["DC: Barrier certificate candidate:", bcCandidate]];
     DCverbose = False;
     {verifiedLie, verifiedUnsafe, verifiedInitial} = 
      Vertification[varSet, LieOrder, rank, flowVec, initialineq, 
       initialeq, unsafeineq, unsafeeq, bcCandidate, domineq, domeq, 
       optimum, DCverbose];
     If[verifiedLie && verifiedUnsafe && verifiedInitial, 
      If[verbose, Print["DC-verification: True!"]]; 
      ansDegree = {barrierTempDegree, TimeUsed[] - time, 4};
      logInfo["Solved by DC at degree " <> ToString[barrierTempDegree] <> "."], 
      If[verbose, Print["DC-verification: False!"]]];
     If[TimeUsed[] - time > timebound && ansDegree[[1]] == 0, 
      ansDegree[[1]] = -1];
     ];
    ];
   ];
  
  
  
  
   For[barrierTempDegree = 1, 
    barrierTempDegree <= (barrierDegree - 3) && ansDegree[[1]] == 0, 
    barrierTempDegree++,
    If[bcTempDefault === Automatic, 
     bcTemp = polyTemp[varSet, a, barrierTempDegree], 
     bcTemp = bcTempDefault; 
     barrierTempDegree = polyDegree[bcTemp, varSet]];
   If[verbose, Print["Vector-DC: Template BC=", bcTemp]];
   
   LieSequence = LieDerivatives[varSet, flowVec, bcTemp, LieOrder];
   If[verbose, Print["Lie sequence: \n", LieSequence]];
   logInfo[
    "Degree " <> ToString[barrierTempDegree] <> ": trying Vector-DC."];
    
    
    vectorNum = 2;
    optimum = 
     VectorBC[varSet, flowVec, bcTemp, LieOrder, rank, initialineq, 
      initialeq, unsafeineq, unsafeeq, domineq, domeq, paraRange, 
      polyAddDegree, LieSequence, \[Epsilon]I, \[Epsilon]U, \[Epsilon]L, 
      vectorNum, \[Epsilon]Vector, \[Delta], seed, verbose, 0];
   If[optimum, 
    ansDegree = {barrierTempDegree, TimeUsed[] - time, 5};
    logInfo[
     "Solved by Vector-DC at degree " <> ToString[barrierTempDegree] <> 
      "."]];
    If[TimeUsed[] - time > timebound && ansDegree[[1]] == 0, 
     ansDegree[[1]] = -1];
    ];
  
  
  logInfo["Total CPU time: " <> ToString[TimeUsed[] - time] <> "s"];
  logInfo["Result tuple (degree,time,methodId): " <> 
    ToString[ansDegree, InputForm]];
  Return[ansDegree];
  ]



identifier[symbols_] := ToExpression[StringJoin[ToString /@ symbols]]


polyDegree[poly_, vars_] := Module[{t},
   Exponent[poly /. Thread[vars -> t*vars], t]
   ];

polyDegreeMax[poly_, vars_] := Module[{deg},
   deg = polyDegree[poly, vars];
   If[ListQ[deg], deg = If[Length[deg] > 0, Max@Flatten[deg], 0]];
   If[deg === -Infinity, deg = 0];
   deg
   ];




polyTemp[vars_, a_, order_] := 
 Module[{n = Length@vars, idx, z, ord = order}, 
  If[ListQ[ord], ord = If[Length[ord] > 0, First@Flatten[ord], 0]];
  If[!NumericQ[ord], ord = 0];
  idx = Cases[Tuples[Range[0, ord], n], x_ /; Plus @@ x <= ord];
  z = Times @@@ (vars^# & /@ idx);
  z . ((Subscript[a, Row[#]]) & /@ idx)
  ]



monomList = 
  Function[{vars, degree}, 
   Module[{deg = degree, n = Length[vars], explist},
    If[ListQ[deg], deg = If[Length[deg] > 0, First@Flatten[deg], 0]];
    If[! NumericQ[deg], deg = 0];
    deg = Max[0, Floor[deg]];
    explist = 
     Flatten[Permutations /@ PadRight[#, {Length@#, n}] &[
         Flatten[IntegerPartitions[#, n] & /@ Range[0, deg], 1]], 
       1] // Transpose;
    Times @@@ Transpose[vars^explist]
    ]
   ];



LieDerivatives[vars_, flow_, bc_, order_] := 
 Module[{Lie, LieSequence, gradient, k},
  Lie = bc;
  LieSequence = {Lie};
  For[k = 1, k <= order, k++,
   gradient = Grad[Lie, vars];
   Lie = Collect[gradient . flow, vars, Simplify];
   AppendTo[LieSequence, Lie];
   ];
  Return[LieSequence];
  ]




coefficientMatrix[vars_, basis_, poly_] := Module[{i, j, A},
  A = Table[
    sym[Min[i, j], Max[i, j]], {i, 0, Length[basis] - 1}, {j, 0, 
     Length[basis] - 1}];
  
  
  Off[Solve::svars];
  A = A /. 
    Solve[Not@Eliminate[Not[basis . A . basis == poly], vars], 
      Flatten[A]][[1]];
  A = A /. sym[_, _] :> 0;
  Return[A];
  ]


normalizeComponents[ineq_, eq_] := Module[{ineqList, eqList, n}, ineqList = If[ListQ[ineq] && ineq =!= {} && AllTrue[ineq, ListQ], ineq, {ineq}]; eqList = If[ListQ[eq] && eq =!= {} && AllTrue[eq, ListQ], eq, {eq}]; n = Max[Length[ineqList], Length[eqList]]; If[Length[ineqList] < n, ineqList = PadRight[ineqList, n, {}]]; If[Length[eqList] < n, eqList = PadRight[eqList, n, {}]]; ineqList = Map[DeleteCases[Flatten[#, Infinity], {}] &, ineqList]; eqList = Map[DeleteCases[Flatten[#, Infinity], {}] &, eqList]; Transpose[{ineqList, eqList}]]
parameterLinkedBCCoff[bcTemp_, bcCoff_, hintVars_] := 
 Module[{targetVars, monomial},
  targetVars = DeleteDuplicates[Flatten[{hintVars}]];
  If[targetVars === {} || bcCoff === {}, Return[{}]];
  Select[bcCoff, monomial = Coefficient[bcTemp, #];
     Length[Intersection[Variables[monomial], targetVars]] > 0 &]
  ]
requireSingleComponent[ineq_, eq_, tag_ : ""] := 
 Module[{comps},
  comps = normalizeComponents[ineq, eq];
  If[Length[comps] > 1,
   If[tag =!= "", 
    Print[tag, ": multiple components are not supported in this method."]];
   Return[$Failed]];
  {comps[[1, 1]], comps[[1, 2]]}
  ]
mergeRange[r1_, r2_] := If[r1 === {} && r2 === {}, {}, If[r1 === {}, r2, If[r2 === {}, r1, {Min[r1[[1]], r2[[1]]], Max[r1[[2]], r2[[2]]]}]]];
linearBoundaryRanges[components_, varSet_, baseRange_] := Module[{ranges, spans, margins, exprs},
 ranges = Table[{}, {Length[varSet]}];
 spans = If[ListQ[baseRange] && Length[baseRange] == Length[varSet] && AllTrue[baseRange, ListQ], baseRange[[All, 2]] - baseRange[[All, 1]], ConstantArray[1, Length[varSet]]];
 margins = Map[Max[0.2 #, 0.5] &, spans];
 exprs = Flatten[components[[All, 1]], 1];
 Do[With[{vars = Variables[expr]},
   If[Length[vars] == 1 && PolynomialQ[expr, vars[[1]]] && Exponent[expr, vars[[1]]] == 1,
    With[{v = vars[[1]], a = Coefficient[expr, vars[[1]], 1], b = expr /. vars[[1]] -> 0},
     If[a =!= 0,
      With[{root = -b/a, idx = FirstPosition[varSet, v, None]},
       If[idx =!= None, ranges[[idx[[1]]]] = Append[ranges[[idx[[1]]]], root]]
       ]
      ]
     ]
    ]
   ]
  , {expr, exprs}];
 Table[If[ranges[[i]] == {}, {}, {Min[ranges[[i]]] - margins[[i]], Max[ranges[[i]]] + margins[[i]]}], {i, 1, Length[varSet]}]
 ]


$WolframScriptOpenImages = True;
$WolframScriptKeepImages = True;
$WolframScriptImageFormat = "png";
$WolframScriptImageDir = Automatic;
$WolframScriptUseTemp = False;
$CaseId =.;
$CaseImageIndex = 0;

showGraphics[graphics_, tag_ : "graphics"] := 
 Module[{useFrontEnd, fmt, dir, base, file},
  useFrontEnd = MatchQ[$FrontEndSession, _FrontEndObject];
  If[useFrontEnd, Print[graphics]; Return[graphics]];
  fmt = If[StringQ[$WolframScriptImageFormat], $WolframScriptImageFormat, "png"];
  If[TrueQ[$WolframScriptUseTemp],
   file = CreateTemporary[FileExtension -> fmt],
   dir = $WolframScriptImageDir;
   If[dir === Automatic || ! StringQ[dir], dir = DirectoryName[$InputFileName]];
   If[dir === "" || dir === $Failed, dir = Directory[]];
  base = 
   If[ValueQ[$CaseId],
     "case-" <> ToString[$CaseId],
     StringReplace[tag, Except[WordCharacter | "-" | "_"] -> "_"]
     ];
   file = FileNameJoin[{dir, base <> "." <> fmt}];
   ];
  Export[file, graphics];
  Print["[graphics exported] ", file];
  If[TrueQ[$WolframScriptOpenImages], Quiet@SystemOpen[file]];
  If[TrueQ[$WolframScriptUseTemp] && ! TrueQ[$WolframScriptKeepImages],
   Quiet@DeleteFile[file]];
  graphics
  ];

renderGraphics2D[varSet_, flowVec_, bc_, initialineq_, initialeq_, 
  unsafeineq_, unsafeeq_, domineq_, domeq_] := 
 Module[{initial, unsafe, domainUnbounded, initialRange, unsafeRange, unsafevars, unsafePointRule, unsafePoint, initialPoint, domain, domainRange, domMin, domMax, graphics, initialSamples, trajPlot, flowPlot, bcPlot, initialPlot, unsafePlot, ranges, i, initialComponents, unsafeComponents, initialPreds, unsafePreds, initialSingle, unsafeSingle, initialIneq, initialEq, unsafeIneq, unsafeEq, minU, maxU, boundaryRange},
  
  initialComponents = normalizeComponents[initialineq, initialeq];
  unsafeComponents = normalizeComponents[unsafeineq, unsafeeq];
  initialPreds = Table[And @@ Join[Table[initialComponents[[ci, 1, i]] >= 0, {i, 1, Length[initialComponents[[ci, 1]]]}], Table[initialComponents[[ci, 2, i]] == 0, {i, 1, Length[initialComponents[[ci, 2]]]}]], {ci, 1, Length[initialComponents]}];
  unsafePreds = Table[And @@ Join[Table[unsafeComponents[[ci, 1, i]] >= 0, {i, 1, Length[unsafeComponents[[ci, 1]]]}], Table[unsafeComponents[[ci, 2, i]] == 0, {i, 1, Length[unsafeComponents[[ci, 2]]]}]], {ci, 1, Length[unsafeComponents]}];
  initial = Or @@ initialPreds; unsafe = Or @@ unsafePreds;
  initialSingle = Length[initialComponents] == 1; unsafeSingle = Length[unsafeComponents] == 1;
  initialIneq = initialComponents[[1, 1]]; initialEq = initialComponents[[1, 2]];
  unsafeIneq = unsafeComponents[[1, 1]]; unsafeEq = unsafeComponents[[1, 2]];
  domain = Join[Table[domineq[[i]] >= 0, {i, 1, Length[domineq]}], Table[domeq[[i]] == 0, {i, 1, Length[domeq]}]];
  
  domainRange = {};
  If[Length[domain] > 0,
   For[i = 1, i <= Length[varSet], i++,
     If[Minimize[{varSet[[i]], domain}, varSet][[1]] >= -N[10^9] && 
        Maximize[{varSet[[i]], domain}, varSet][[1]] <= N[10^9],
       domMin = Minimize[{varSet[[i]], domain}, varSet][[1]];
       domMax = Maximize[{varSet[[i]], domain}, varSet][[1]];
       AppendTo[
        domainRange, {domMin - (domMax - domMin)/10, 
         domMax + (domMax - domMin)/10}],
       domainRange = {}; Break[];];
     ];
   ];
  
  
  If[Length[domainRange] == 0,
   domainUnbounded = 1;
   domainRange = {};
   
   
   initialRange = {};
   For[i = 1, i <= Length[varSet], i++,
    If[Minimize[{varSet[[i]], initial}, varSet][[1]] >= -N[10^9] && 
       Maximize[{varSet[[i]], initial}, varSet][[1]] <= N[10^9],
      AppendTo[initialRange, 
       N[{Minimize[{varSet[[i]], initial}, varSet][[1]], 
         Maximize[{varSet[[i]], initial}, varSet][[1]]}]],
      initialRange = {}; Break[];];
    ];
   
   unsafeRange = {};
   For[i = 1, i <= Length[varSet], i++,
    minU = Quiet[Minimize[{varSet[[i]], unsafe}, varSet][[1]]];
    maxU = Quiet[Maximize[{varSet[[i]], unsafe}, varSet][[1]]];
    If[And[minU >= -N[10^7] && maxU <= N[10^7], minU =!= Infinity, maxU =!= Infinity, minU =!= -Infinity, maxU =!= -Infinity],
      AppendTo[unsafeRange, N[{minU, maxU}]],
      unsafeRange = {}; Break[];];
    ];
   boundaryRange = linearBoundaryRanges[unsafeComponents, varSet, initialRange];
   If[Length[unsafeRange] == 0 && AnyTrue[boundaryRange, # =!= {} &], 
    unsafeRange = Table[mergeRange[If[Length[initialRange] == Length[varSet], initialRange[[i]], {}], boundaryRange[[i]]], {i, 1, Length[varSet]}];
    unsafeRange = Table[If[unsafeRange[[i]] == {}, {-1, 1}, unsafeRange[[i]]], {i, 1, Length[varSet]}]];

   
   
   
   If[Length[unsafeRange] == 0 && Length[initialRange] > 0, unsafeRange = initialRange];

   
   
   
   If[Length[initialRange] == 0 && Length[unsafeRange] > 0, initialRange = unsafeRange];

   
   
   
   If[Length[unsafeRange] == 0 || Length[initialRange] == 0,
    unsafevars = Table[Subscript[a, i], {i, 1, Length[varSet]}];
    
    
    unsafePointRule = 
     Minimize[{Norm[unsafevars - varSet], 
        And[initial, unsafe /. (Thread[varSet -> unsafevars])]}, 
       Join[varSet, unsafevars]][[2]];
    
    unsafePoint = N[(2*unsafevars - varSet) /. unsafePointRule];
    initialPoint = N[(2*varSet - unsafevars) /. unsafePointRule];
    
    If[Length[initialRange] == 0,
     If[Length[unsafeRange] == 0,
      For[i = 1, i <= Length[varSet], i++, 
       domMin = Min[initialPoint[[i]], unsafePoint[[i]]]; 
       domMax = Max[initialPoint[[i]], unsafePoint[[i]]]; 
       AppendTo[
        domainRange, {domMin - (domMax - domMin)/10, 
         domMax + (domMax - domMin)/10}]],
      
      For[i = 1, i <= Length[varSet], i++, 
       domMin = Min[initialPoint[[i]], unsafeRange[[i]][[1]]]; 
       domMax = Max[initialPoint[[i]], unsafeRange[[i]][[2]]]; 
       AppendTo[
        domainRange, {domMin - (domMax - domMin)/10, 
         domMax + (domMax - domMin)/10}]]
      ],
     
     For[i = 1, i <= Length[varSet], i++, 
      domMin = Min[initialRange[[i]][[1]], unsafePoint[[i]]]; 
      domMax = Max[initialRange[[i]][[2]], unsafePoint[[i]]]; 
      AppendTo[
       domainRange, {domMin - (domMax - domMin)/10, 
        domMax + (domMax - domMin)/10}]];
     ],
    
    For[i = 1, i <= Length[varSet], i++, 
     domMin = Min[initialRange[[i]][[1]], unsafeRange[[i]][[1]]]; 
     domMax = Max[initialRange[[i]][[2]], unsafeRange[[i]][[2]]]; 
     AppendTo[
      domainRange, {domMin - (domMax - domMin)/10, 
       domMax + (domMax - domMin)/10}]];
    ];
   
   For[i = 1, i <= Length[varSet], i++,
    If[domainRange[[i]][[2]] - domainRange[[i]][[1]] <= N[10^8],
      domainRange[[i]][[2]] = 
       domainRange[[i]][[2]] + 
        0.5*Max[Join @@ (domainRange[[1 ;; Length[varSet], 2 ;; 2]] - 
             domainRange[[1 ;; Length[varSet], 1 ;; 1]])];
      domainRange[[i]][[1]] = 
       domainRange[[i]][[1]] - 
        0.5*Max[Join @@ (domainRange[[1 ;; Length[varSet], 2 ;; 2]] - 
             domainRange[[1 ;; Length[varSet], 1 ;; 1]])];];
    ];
   
   ];
  
  ranges = 
   Table[Prepend[domainRange[[i]], varSet[[i]]], {i, 1, 
     Length[varSet]}];
  ranges = Sequence @@ ranges;
  
  
  If[initialSingle && Length[initialIneq] == 0 && Length[initialEq] == Length[varSet], 
   initialSamples = 
    varSet /. 
     Solve[Table[initialEq[[i]] == 0, {i, 1, Length[initialEq]}], 
      varSet], 
   initialSamples = 
     RandomPoint[
      ImplicitRegion[initial, varSet], 20];];
  
  
  Off[NDSolve::ndsz];
  traj[x0_] := 
   NDSolve[Join[
     Thread[#'[t] & /@ 
        varSet == (flowVec /. 
         Table[varSet[[i]] -> varSet[[i]][t], {i, 1, 
           Length[varSet]}])], Thread[#[0] & /@ varSet == x0]], 
    varSet, {t, 0, 20}, Method -> "StiffnessSwitching"];
  trajPlot = 
   ParametricPlot[
    Evaluate[(#[t] & /@ varSet) /. traj[#] & /@ initialSamples], {t, 
     0, 20}, RegionFunction -> ((domainRange[[1]][[1]] <= #1 <= 
          domainRange[[1]][[2]]) && (domainRange[[2]][[1]] <= #2 <= 
          domainRange[[2]][[2]]) &), 
    PlotStyle -> Directive[Black, Thickness[Medium]]];
  
  
  
  flowPlot = 
   VectorPlot[flowVec, Evaluate[ranges], VectorScaling -> Automatic, 
    VectorSizes -> Automatic, VectorColorFunction -> None, 
    VectorStyle -> Gray];
  If[initialSingle && Length[initialIneq] == 0 && Length[initialEq] == Length[varSet], 
   initialPlot = 
    RegionPlot[
     And @@ Join[
       Table[initialeq[[i]] <= 0.2, {i, 1, Length[initialeq]}], 
       Table[initialeq[[i]] >= -0.2, {i, 1, Length[initialeq]}]], 
     Evaluate[ranges], PlotStyle -> Directive[Blue], 
     PlotLegends -> 
      SwatchLegend[{"\[ScriptCapitalI](\!\(\*StyleBox[\"x\",FontWeight->\"Bold\"]\)) \[LessEqual] 0"}]], 
   initialPlot = 
     RegionPlot[
      initial, 
      Evaluate[ranges], PlotStyle -> Directive[Blue], 
      PlotLegends -> 
       SwatchLegend[{"\[ScriptCapitalI](\!\(\*StyleBox[\"x\",FontWeight->\"Bold\"]\)) \[LessEqual] 0"}]];];
  
  If[unsafeSingle && Length[unsafeIneq] == 0 && Length[unsafeEq] == Length[varSet], 
   unsafePlot = 
    RegionPlot[
     And @@ Join[
       Table[unsafeEq[[i]] <= 0.1, {i, 1, Length[unsafeEq]}], 
       Table[unsafeEq[[i]] >= -0.1, {i, 1, Length[unsafeEq]}]], 
     Evaluate[ranges], PlotStyle -> Directive[Red], 
     PlotLegends -> 
      SwatchLegend[{"\[ScriptCapitalU](\!\(\*StyleBox[\"x\",FontWeight->\"Bold\"]\)) \[LessEqual] 0"}]], 
   unsafePlot = 
     RegionPlot[
      unsafe, 
      Evaluate[ranges], PlotStyle -> Directive[Red], 
      PlotLegends -> 
       SwatchLegend[{"\[ScriptCapitalU](\!\(\*StyleBox[\"x\",FontWeight->\"Bold\"]\)) \[LessEqual] 0"}]];];
  
  
  
  If[Length[bc /. Thread[varSet -> 0]] == 0, 
   bcPlot = 
    RegionPlot[bc <= 0, Evaluate[ranges], BoundaryStyle -> {Dashed}, 
     PlotStyle -> Directive[Opacity[.6], LightPink], 
     PlotLegends -> 
      SwatchLegend[{"\!\(\*StyleBox[\"B\",FontSlant->\"Italic\"]\)(\!\(\*StyleBox[\"x\",FontWeight->\"Bold\"]\)) \[LessEqual] 0"}]], 
   bcPlot = 
    RegionPlot[And @@ Table[bc[[i]] <= 0, {i, 1, Length[bc]}], 
     Evaluate[ranges], BoundaryStyle -> {Dashed}, 
     PlotStyle -> Directive[Opacity[.6], LightPink], 
     PlotLegends -> 
      SwatchLegend[{"\!\(\*StyleBox[\"B\",FontSlant->\"Italic\"]\)(\!\(\*StyleBox[\"x\",FontWeight->\"Bold\"]\)) \[LessEqual] 0"}]]];
  
  graphics = 
   Show[flowPlot, initialPlot, unsafePlot, bcPlot, trajPlot, 
    Frame -> True, FrameLabel -> varSet, RotateLabel -> False];
  showGraphics[graphics, 
   "render2D-" <> StringRiffle[ToString /@ varSet, "_"]];
  Return[graphics];
  ]




renderGraphics3D[varSet_, flowVec_, bc_, initialineq_, initialeq_, 
  unsafeineq_, unsafeeq_, domineq_, domeq_] := 
 Module[{initial, unsafe, domain, domainRange, domMin, domMax, graphics, initialSamples, trajPlot, bcPlot, initialPlot, unsafePlot, ranges, i, initialComponents, unsafeComponents, initialPreds, unsafePreds, initialSingle, unsafeSingle, initialIneq, initialEq, unsafeIneq, unsafeEq},
  initialComponents = normalizeComponents[initialineq, initialeq];
  unsafeComponents = normalizeComponents[unsafeineq, unsafeeq];
  initialPreds = Table[And @@ Join[Table[initialComponents[[ci, 1, i]] >= 0, {i, 1, Length[initialComponents[[ci, 1]]]}], Table[initialComponents[[ci, 2, i]] == 0, {i, 1, Length[initialComponents[[ci, 2]]]}]], {ci, 1, Length[initialComponents]}];
  unsafePreds = Table[And @@ Join[Table[unsafeComponents[[ci, 1, i]] >= 0, {i, 1, Length[unsafeComponents[[ci, 1]]]}], Table[unsafeComponents[[ci, 2, i]] == 0, {i, 1, Length[unsafeComponents[[ci, 2]]]}]], {ci, 1, Length[unsafeComponents]}];
  initial = Or @@ initialPreds; unsafe = Or @@ unsafePreds;
  initialSingle = Length[initialComponents] == 1; unsafeSingle = Length[unsafeComponents] == 1;
  initialIneq = initialComponents[[1, 1]]; initialEq = initialComponents[[1, 2]];
  unsafeIneq = unsafeComponents[[1, 1]]; unsafeEq = unsafeComponents[[1, 2]];
  domain = Join[Table[domineq[[i]] >= 0, {i, 1, Length[domineq]}], Table[domeq[[i]] == 0, {i, 1, Length[domeq]}]];
  domainRange = {};
  For[i = 1, i <= Length[varSet], i++,
   domMin = 
    Min[Minimize[{varSet[[i]], initial}, varSet][[1]], 
     Minimize[{varSet[[i]], unsafe}, varSet][[1]]];
   
   If[Length[domain] > 0, 
    domMin = 
     Min[Minimize[{varSet[[i]], domain}, varSet][[1]], domMin]];
   domMax = 
    Max[Maximize[{varSet[[i]], initial}, varSet][[1]], 
     Maximize[{varSet[[i]], unsafe}, varSet][[1]]];
   
   If[Length[domain] > 0, 
    domMax = 
     Max[Maximize[{varSet[[i]], domain}, varSet][[1]], domMax]];
   AppendTo[
    domainRange, {domMin - (domMax - domMin)/20, 
     domMax + (domMax - domMin)/20}];
   ];
  ranges = 
   Table[Prepend[domainRange[[i]], varSet[[i]]], {i, 1, 
     Length[varSet]}];
  ranges = Sequence @@ ranges;
  
  If[initialSingle && Length[initialIneq] == 0 && Length[initialEq] == Length[varSet], 
   initialSamples = 
    varSet /. 
     Solve[Table[initialEq[[i]] == 0, {i, 1, Length[initialEq]}], 
      varSet], 
   initialSamples = 
     RandomPoint[
      ImplicitRegion[initial, varSet], 3];];
  
  Off[NDSolve::ndsz];
  traj[x0_] := 
   NDSolve[Join[
     Thread[#'[t] & /@ 
        varSet == (flowVec /. 
         Table[varSet[[i]] -> varSet[[i]][t], {i, 1, 
           Length[varSet]}])], Thread[#[0] & /@ varSet == x0]], 
    varSet, {t, 0, 20}, Method -> "StiffnessSwitching"];
  trajPlot = 
   ParametricPlot3D[
    Evaluate[(#[t] & /@ varSet) /. traj[#] & /@ initialSamples], {t, 
     0, 20}, RegionFunction -> ((domainRange[[1]][[1]] <= #1 <= 
          domainRange[[1]][[2]]) && (domainRange[[2]][[1]] <= #2 <= 
          domainRange[[2]][[2]]) && (domainRange[[3]][[1]] <= #3 <= 
          domainRange[[3]][[2]]) &), PlotStyle -> Black];
  
  
  If[initialSingle && Length[initialIneq] == 0 && Length[initialEq] == Length[varSet], 
   initialPlot = 
    RegionPlot3D[
     And @@ Join[
       Table[initialeq[[i]] <= 0.1, {i, 1, Length[initialeq]}], 
       Table[initialeq[[i]] >= -0.1, {i, 1, Length[initialeq]}]], 
     Evaluate[ranges], PlotStyle -> Directive[Blue], 
     PlotLegends -> 
      SwatchLegend[{"\[ScriptCapitalI](\!\(\*StyleBox[\"x\",FontWeight->\"Bold\"]\)) \[LessEqual] 0"}]], 
   initialPlot = 
     RegionPlot3D[
      initial, 
      Evaluate[ranges], PlotStyle -> Directive[Blue], 
      PlotLegends -> 
       SwatchLegend[{"\[ScriptCapitalI](\!\(\*StyleBox[\"x\",FontWeight->\"Bold\"]\)) \[LessEqual] 0"}]];];
  
  
  If[unsafeSingle && Length[unsafeIneq] == 0 && Length[unsafeEq] == Length[varSet], 
   unsafePlot = 
    RegionPlot3D[
     And @@ Join[
       Table[unsafeEq[[i]] <= 0.1, {i, 1, Length[unsafeEq]}], 
       Table[unsafeEq[[i]] >= -0.1, {i, 1, Length[unsafeEq]}]], 
     Evaluate[ranges], PlotStyle -> Directive[Red], 
     PlotLegends -> 
      SwatchLegend[{"\[ScriptCapitalU](\!\(\*StyleBox[\"x\",FontWeight->\"Bold\"]\)) \[LessEqual] 0"}]], 
   unsafePlot = 
     RegionPlot3D[
      unsafe, 
      Evaluate[ranges], PlotStyle -> Directive[Red], 
      PlotLegends -> 
       SwatchLegend[{"\[ScriptCapitalU](\!\(\*StyleBox[\"x\",FontWeight->\"Bold\"]\)) \[LessEqual] 0"}]];];
  
  
  If[Length[bc /. Thread[varSet -> 0]] == 0, 
   bcPlot = 
    RegionPlot3D[bc <= 0, Evaluate[ranges], 
     PlotStyle -> Directive[Opacity[.2], Pink], 
     MeshStyle -> Opacity[0.4], 
     PlotLegends -> 
      SwatchLegend[{"\!\(\*StyleBox[\"B\",FontSlant->\"Italic\"]\)(\!\(\*StyleBox[\"x\",FontWeight->\"Bold\"]\)) \[LessEqual] 0"}]],
   bcPlot = 
    RegionPlot3D[And @@ Table[bc[[i]] <= 0, {i, 1, Length[bc]}], 
     Evaluate[ranges], PlotStyle -> Directive[Opacity[.2], Pink], 
     MeshStyle -> Opacity[0.4], 
     PlotLegends -> 
      SwatchLegend[{"\!\(\*StyleBox[\"B\",FontSlant->\"Italic\"]\)(\!\(\*StyleBox[\"x\",FontWeight->\"Bold\"]\)) \[LessEqual] 0"}]]];
  graphics = 
   Show[initialPlot, unsafePlot, bcPlot, trajPlot, Frame -> True, 
    FrameLabel -> varSet, RotateLabel -> False];
  showGraphics[graphics, 
   "render3D-" <> StringRiffle[ToString /@ varSet, "_"]];
  Return[graphics];
  
  ]


degreeDecision[frontDegree_, polyAddDegree_, ineq_, eq_, varSet_] := 
  Module[{polyTargetDegree, ineqdegree, eqdegree, sosdegree, polydegree, ineqFlat, eqFlat},
   
   If[Length[varSet] >= 6, 
    Return[Table[0, {i, 1, Length[ineq] + Length[eq]}]]];
   ineqFlat = Flatten[ineq, Infinity];
   eqFlat = Flatten[eq, Infinity];
   If[!ListQ[ineqFlat], ineqFlat = {ineqFlat}];
   If[!ListQ[eqFlat], eqFlat = {eqFlat}];
   polyTargetDegree = frontDegree + polyAddDegree;
   ineqdegree = Map[polyDegree[#, varSet] &, ineqFlat];
   eqdegree = Map[polyDegree[#, varSet] &, eqFlat];
  If[Max[Join[ineqdegree, eqdegree]] > polyTargetDegree, 
   polyTargetDegree = Max[Join[ineqdegree, eqdegree]]; 
    logDebug[
     "frontDegree+polyAddDegree is lower than ineq/eq degree; auto-increasing target degree."]];
   sosdegree = Table[0, {i, Length[ineqFlat]}];
   polydegree = Table[0, {i, Length[eqFlat]}];
   For[i = 1, i <= Length[ineqFlat], i++,
    If[Mod[polyTargetDegree - ineqdegree[[i]], 2] == 1, 
      sosdegree[[i]] = polyTargetDegree - ineqdegree[[i]] + 1, 
      sosdegree[[i]] = polyTargetDegree - ineqdegree[[i]]];
    ];
   For[i = 1, i <= Length[eqFlat], i++,
    polydegree[[i]] = polyTargetDegree - eqdegree[[i]];
    ];
   Return[Join[sosdegree, polydegree]];
   ];


matrixLiteralScale[matrix_] := 
 Module[{nums},
  nums = Cases[matrix, x_?NumericQ :> Abs[N[x]], Infinity];
  If[Length[nums] == 0, 1., Max[1., Max[nums]]]
  ];

normalizeLMIMatrix[matrix_] := matrix/matrixLiteralScale[matrix];

makeSemidefiniteConeConstraints[matrixSet_] := 
 Module[{normalized},
  normalized = normalizeLMIMatrix /@ matrixSet;
  Table[VectorLessEqual[{normalized[[i]], 0}, {SemidefiniteCone, 
     Dimensions[normalized[[i]]][[1]]}], {i, 1, Length[normalized]}]
  ];

safeSemidefiniteOptimization[objective_, matrixSet_, extraConstraints_,
    vars_, resultSpec_, extraOptions___Rule] := 
 Module[{constraints, result, solverVars, fallbackPoint, timeoutToken, msgList},
  solverVars = DeleteDuplicates[Flatten[{vars}]];
  fallbackPoint = 
   Thread[solverVars -> ConstantArray[0., Length[solverVars]]];
  constraints = 
   Join[makeSemidefiniteConeConstraints[matrixSet], 
    Flatten[{extraConstraints}]];
  timeoutToken = Unique["SDPTimeout"];
  $LastSDPStatus = "ok";
  result = 
   TimeConstrained[
    Block[{$MessageList = {}},
      msgList = {};
      result = 
       Quiet[
        Check[
         SemidefiniteOptimization[objective, constraints, vars, resultSpec,
            Sequence @@ $SDPPrimaryOptions, extraOptions], 
         ($LastSDPStatus = "nonconvex"; $Failed), 
         {SemidefiniteOptimization::ctnc}], 
        {SemidefiniteOptimization::ctnc, SemidefiniteOptimization::parsuc}];
      msgList = $MessageList;
      If[AnyTrue[msgList, 
        StringContainsQ[ToString[#, InputForm], 
          "SemidefiniteOptimization::parsuc"] &], 
       $LastSDPStatus = "partial_success"];
      result
      ], $SDPCallTimeLimit, timeoutToken];
  If[result === timeoutToken, $LastSDPStatus = "timeout"; 
   Return[{fallbackPoint, Infinity}]];
  If[result === $Failed,
   If[$LastSDPStatus =!= "nonconvex", $LastSDPStatus = "solver_error"];
   Return[{fallbackPoint, Infinity}]];
  If[! (ListQ[result] && Length[result] == 2),
   If[Head[result] === SemidefiniteOptimization, $LastSDPStatus = "unevaluated", 
    $LastSDPStatus = "bad_return"];
   If[TrueQ[$SDPWarnOnFailure], 
    logWarn[
     "SDP returned unexpected format (status=" <> $LastSDPStatus <> 
      ", head=" <> ToString[Head[result]] <> 
      "). Using zero fallback point."]];
   result = {fallbackPoint, Infinity}];
  result
  ];

safeCoeffScale[values_] := 
 Module[{nums},
  nums = Cases[values, x_?NumericQ :> Abs[N[x]], Infinity];
  If[Length[nums] == 0, 1., Max[10^-12, Max[nums]]]
  ];


Initial[cMatrixSet_, SDPVars_, positiveCoff_, sigmaCoff_, polyCoff_, 
   paraRange_, verbose_, part_ : False, initialVector1_ : Automatic] :=
   Module[{initialrules, initialVector, initialSDPVars, paraRegion, point, maximum},
   SDPVars = DeleteDuplicates[Flatten[SDPVars]];
   sigmaCoff = DeleteDuplicates[Flatten[sigmaCoff]];
   polyCoff = DeleteDuplicates[Flatten[polyCoff]];
   positiveCoff = DeleteDuplicates[Flatten[positiveCoff]];
   If[initialVector1 === Automatic && Length[positiveCoff] == 0,
    initialrules = 
     Join[Thread[
       polyCoff -> 
        RandomReal[{paraRange[[1]], 
          paraRange[[2]]}, {Length[polyCoff]}]], 
      Thread[DeleteCases[sigmaCoff, \[Lambda]] -> 
        RandomReal[{paraRange[[1]], 
          paraRange[[2]]}, {Length[sigmaCoff] - 1}]]];
    
    If[verbose, Print["initialrules=", initialrules]],
    If[Length[positiveCoff] > 0 && initialVector1 === Automatic,
     initialrules = 
      Thread[positiveCoff -> 
        RandomReal[{0, paraRange[[2]]}, {Length[positiveCoff]}]]; 
     initialVector = Join[sigmaCoff, polyCoff] /. initialrules,
     initialVector = Join[sigmaCoff, polyCoff] /. initialVector1; 
     initialrules = initialVector1];
    initialSDPVars = DeleteCases[initialVector, _?NumericQ];
    initialrules = 
     Join[initialrules, 
      Thread[DeleteCases[initialSDPVars, \[Lambda]] -> 
        RandomReal[{paraRange[[1]], 
          paraRange[[2]]}, {Length[initialSDPVars] - 1}]]];
    If[verbose, Print["initialrules=", initialrules]];
    
    ];
   initialVector = Flatten[SDPVars /. initialrules];
   If[verbose, Print["Initial vector:\n", initialVector]];
   If[part, Return[initialVector]];
   initialSDPVars = 
    DeleteDuplicates[Flatten[DeleteCases[initialVector, _?NumericQ]]];
   paraRegion = 
    Cuboid[Table[paraRange[[1]], Length[initialSDPVars] - 1], 
     Table[paraRange[[2]], Length[initialSDPVars] - 1]];
  {point, maximum} = 
   safeSemidefiniteOptimization[-\[Lambda], (cMatrixSet /. initialrules),
     {DeleteCases[initialSDPVars, \[Lambda]] \[Element] paraRegion}, 
    initialSDPVars, {"PrimalMinimizerRules", "PrimalMinimumValue"}];
   Return[initialVector /. point];
   ];

Vertification[varSet_, LieOrder_, rank_, flowVec_, initialineq_, 
   initialeq_, unsafeineq_, unsafeeq_, bcCandidate_, domineq_, domeq_,
    optimum_, verbose_] := 
  Module[{verifiedInitial, verifiedUnsafe, QECheckLie, verifiedLie, LieSequence, bcCandidateSet, LieSequenceSet, initialComponents, unsafeComponents, initialPreds, unsafePreds},
   Off[Reduce::ratnz, General::notfound, General::infy, 
    General::indet, ReplaceAll::reps];
   
   If[Length[bcCandidate /. Thread[varSet -> 0]] == 0,
    LieSequence = 
     LieDerivatives[varSet, flowVec, bcCandidate, LieOrder];
    If[verbose, Print["LieSequence=", LieSequence]];
    initialComponents = normalizeComponents[initialineq, initialeq];
    unsafeComponents = normalizeComponents[unsafeineq, unsafeeq];
    initialPreds = Table[And @@ Join[Table[initialComponents[[ci, 1, i]] >= 0, {i, 1, Length[initialComponents[[ci, 1]]]}], Table[initialComponents[[ci, 2, i]] == 0, {i, 1, Length[initialComponents[[ci, 2]]]}]], {ci, 1, Length[initialComponents]}];
    unsafePreds = Table[And @@ Join[Table[unsafeComponents[[ci, 1, i]] >= 0, {i, 1, Length[unsafeComponents[[ci, 1]]]}], Table[unsafeComponents[[ci, 2, i]] == 0, {i, 1, Length[unsafeComponents[[ci, 2]]]}]], {ci, 1, Length[unsafeComponents]}];
    verifiedInitial = Reduce[ForAll[varSet, And @@ Table[initialPreds[[i]] \[Implies] bcCandidate <= 0, {i, 1, Length[initialPreds]}]], Reals];
    verifiedUnsafe = Reduce[ForAll[varSet, And @@ Table[bcCandidate <= 0 \[Implies] Or @@ Join[Table[unsafeComponents[[i, 1, j]] < 0, {j, 1, Length[unsafeComponents[[i, 1]]]}], Table[unsafeComponents[[i, 2, j]] > 0, {j, 1, Length[unsafeComponents[[i, 2]]]}], Table[unsafeComponents[[i, 2, j]] < 0, {j, 1, Length[unsafeComponents[[i, 2]]]}]], {i, 1, Length[unsafeComponents]}]], Reals];
    
    
    If[LieOrder > 1,
     QECheckLie = 
      If[LieOrder < rank, 
       ForAll[varSet, 
        And @@ Join[Table[domineq[[i]] >= 0, {i, 1, Length[domineq]}],
            Table[domeq[[i]] == 0, {i, 1, Length[domeq]}]]
         \[Implies] 
         And @@ Append[
           Table[(And @@ 
               Thread[(Drop[LieSequence, {i, Length[LieSequence]}] /. 
                   optimum) == 0]) \[Implies] (LieSequence[[i]] /. 
                optimum) <= 0,
            {i, 2, 
             Length[LieSequence] - 1}], (And @@ 
              Thread[(Drop[LieSequence, -1] /. optimum) == 
                0]) \[Implies] (LieSequence[[-1]] /. optimum) < 0]],
       
       
       ForAll[varSet, 
        And @@ Join[Table[domineq[[i]] >= 0, {i, 1, Length[domineq]}],
            Table[domeq[[i]] == 0, {i, 1, Length[domeq]}]]
         \[Implies] 
         And @@ Table[(And @@ 
              Thread[(Drop[LieSequence, {i, Length[LieSequence]}] /. 
                  optimum) == 0])
            \[Implies] (LieSequence[[i]] /. optimum) <= 0, {i, 2, 
            Length[LieSequence]}]]],
     
     
     QECheckLie = 
      If[Length[domineq] + Length[domeq] > 0, 
       ForAll[varSet, 
        And @@ Join[Table[domineq[[i]] >= 0, {i, 1, Length[domineq]}],
            Table[domeq[[i]] == 0, {i, 1, Length[domeq]}]]
         \[Implies] 
         And @@ Table[(And @@ 
              Thread[(Drop[LieSequence, {i, Length[LieSequence]}] /. 
                  optimum) == 0]) \[Implies] (LieSequence[[i]] /. 
               optimum) < 0, {i, 2, Length[LieSequence]}]], 
       ForAll[varSet, 
        And @@ Table[(And @@ 
             Thread[(Drop[LieSequence, {i, Length[LieSequence]}] /. 
                 optimum) == 0]) \[Implies] (LieSequence[[i]] /. 
              optimum) < 0, {i, 2, 
           Length[LieSequence]}]]]
     
     ];
    
    verifiedLie = Reduce[QECheckLie, Reals];
    If[verbose, 
     Print["verifiedInitial=", verifiedInitial, "   verifiedUnsafe=", 
      verifiedUnsafe, "    verifiedLie=", verifiedLie]];
    
    If[Or[verbose, 
      And @@ {verifiedInitial, verifiedUnsafe, And @@ verifiedLie}],
     If[Length[varSet] == 2, 
      renderGraphics2D[varSet, flowVec, bcCandidate, initialineq, 
       initialeq, unsafeineq, unsafeeq, domineq, domeq],
      If[Length[varSet] == 3, 
       renderGraphics3D[varSet, flowVec, bcCandidate, initialineq, 
        initialeq, unsafeineq, unsafeeq, domineq, domeq]]]];
    If[TrueQ[
      And @@ {verifiedInitial, verifiedUnsafe, And @@ verifiedLie}],
     Print["Verified barrier certificate: ", bcCandidate]];
    Return[{verifiedInitial, verifiedUnsafe, verifiedLie}],
    
    
    
    bcCandidateSet = bcCandidate;
    LieSequenceSet = 
     Table[LieDerivatives[varSet, flowVec, bcCandidateSet[[i]], 
       1], {i, 1, Length[bcCandidateSet]}];
    
    initialComponents = normalizeComponents[initialineq, initialeq];
    unsafeComponents = normalizeComponents[unsafeineq, unsafeeq];
    initialPreds = 
     Table[And @@ Join[
        Table[initialComponents[[ci, 1, i]] >= 0, {i, 1, 
          Length[initialComponents[[ci, 1]]]}], 
        Table[initialComponents[[ci, 2, i]] == 0, {i, 1, 
          Length[initialComponents[[ci, 2]]]}]], {ci, 1, 
       Length[initialComponents]}];
    unsafePreds = 
     Table[And @@ Join[
        Table[unsafeComponents[[ci, 1, i]] >= 0, {i, 1, 
          Length[unsafeComponents[[ci, 1]]]}], 
        Table[unsafeComponents[[ci, 2, i]] == 0, {i, 1, 
          Length[unsafeComponents[[ci, 2]]]}]], {ci, 1, 
       Length[unsafeComponents]}];
    verifiedInitial = 
     Reduce[ForAll[varSet, 
       And @@ Table[
          initialPreds[[ci]] \[Implies] 
           And @@ 
            Table[bcCandidateSet[[i]] <= 0, {i, 1, 
              Length[bcCandidateSet]}], {ci, 1, 
           Length[initialPreds]}]], Reals];
    
    verifiedUnsafe = 
     Reduce[ForAll[varSet, 
       And @@ Table[
          unsafePreds[[ci]] \[Implies] 
           Or @@ Table[bcCandidateSet[[bi]] > 0, {bi, 1, 
              Length[bcCandidateSet]}], {ci, 1, 
            Length[unsafePreds]}]], Reals];
    
    
    
    
    QECheckLie = 
     Table[ForAll[varSet, 
       And @@ Join[Table[domineq[[i]] >= 0, {i, 1, Length[domineq]}], 
          Table[domeq[[i]] == 0, {i, 1, 
            Length[domeq]}]] \[Implies] (And @@ 
           Join[{bcCandidateSet[[i]] == 0}, 
            Drop[Table[
              bcCandidateSet[[i]] <= 0, {i, 1, 
               Length[bcCandidateSet]}], {i}]] \[Implies] 
          LieSequenceSet[[i]][[2]] < 0)], {i, 1, 
       Length[bcCandidateSet]}];
    
    
    verifiedLie = 
     Table[Reduce[QECheckLie[[i]], Reals], {i, 1, Length[QECheckLie]}];
    
    If[verbose, 
     Print["verifiedInitial=", verifiedInitial, "   verifiedUnsafe=", 
      verifiedUnsafe, "    verifiedLie=", verifiedLie]];
    
    
    
    If[Or[verbose, 
      And @@ {verifiedInitial, verifiedUnsafe, And @@ verifiedLie}],
     If[Length[varSet] == 2, 
      renderGraphics2D[varSet, flowVec, bcCandidate, initialineq, 
       initialeq, unsafeineq, unsafeeq, domineq, domeq],
      If[Length[varSet] == 3, 
       renderGraphics3D[varSet, flowVec, bcCandidate, initialineq, 
        initialeq, unsafeineq, unsafeeq, domineq, domeq]]]];
    If[TrueQ[
      And @@ {verifiedInitial, verifiedUnsafe, And @@ verifiedLie}],
     Print["Verified barrier certificate set: ", bcCandidateSet]];
    Return[{verifiedInitial, verifiedUnsafe, And @@ verifiedLie}];
    ];
   ];

DC[varSet_, flowVec_, rank_, domineq_, domeq_, initialineq_, 
  initialeq_, unsafeineq_, unsafeeq_, paraRange_, 
  LieOrder_, \[Epsilon]DC_, \[Delta]_, bcTemp_, cMatrixSet_, 
  dcpositiveCoff_, dcsigmaCoff_, dcpolyCoff_, round_, 
  verbose_ : False, initialVector1_ : Automatic] := 
  Module[{DCTime, cMatrix, coff, bcCoff, interCoff, polyCoff, SDPVars, point, maximum, i, j, k, n, paraRegion, LMISet, matC, matH, matG, matF, dcstatus, matOmegaH, matOmegaG, matGamma, matM, matI, matKronecker, eigenValues, eigenVectors, matD, matV, matDPlus, matDMinus, matM1, matM2, BMI2, matN, zCoff, matNzI, matLinear, BMI2Rules, zkCoff, dBMI2, matCorner, matCornerUT1, matCornerUT2, initialVector, LMIConstraint, optimumSequence, optimum, solutionDist, tmp, initIneq, initEq, unsafeIneqLocal, unsafeEqLocal},
  
  
  initIneq = initialineq;
  initEq = initialeq;
  unsafeIneqLocal = unsafeineq;
  unsafeEqLocal = unsafeeq;
  tmp = normalizeComponents[initIneq, initEq];
  initIneq = 
   DeleteCases[Flatten[tmp[[All, 1]], Infinity], {}];
  initEq = 
   DeleteCases[Flatten[tmp[[All, 2]], Infinity], {}];
  tmp = normalizeComponents[unsafeIneqLocal, unsafeEqLocal];
  unsafeIneqLocal = 
   DeleteCases[Flatten[tmp[[All, 1]], Infinity], {}];
  unsafeEqLocal = 
   DeleteCases[Flatten[tmp[[All, 2]], Infinity], {}];
  If[! ListQ[initIneq], initIneq = {initIneq}];
  If[! ListQ[initEq], initEq = {initEq}];
  If[! ListQ[unsafeIneqLocal], unsafeIneqLocal = {unsafeIneqLocal}];
  If[! ListQ[unsafeEqLocal], unsafeEqLocal = {unsafeEqLocal}];
  
  DCTime = TimeUsed[];
  LMISet = {};
  SDPVars = {};
  dcstatus = False;
  
  For[n = 1, n <= Length[cMatrixSet], n++,
   cMatrix = cMatrixSet[[n]];
   
   
   
   coff = Variables[cMatrix];
   bcCoff = Cases[coff, Subscript[a, _]];
   If[Length[bcCoff] == 0, 
    bcCoff = 
     Join @@ Table[
       Cases[coff, 
        Subscript[ToExpression[StringJoin[ToString /@ {a, i}]], 
         Row[_]]], {i, 1, Length[bcTemp]}]];
   interCoff = Cases[coff, Subscript[b, _]];
   If[Length[bcCoff] + Length[interCoff] == 0, 
    AppendTo[LMISet, cMatrix]; Continue[]];
   If[Length[bcCoff] == 0, bcCoff = interCoff];
   polyCoff = Complement[coff, bcCoff];
   
   matC = cMatrix /. Thread[coff -> 0];
   matH = 
    Table[Coefficient[
      cMatrix /. Thread[Cases[coff, Except[bcCoff[[i]]]] -> 0], 
      bcCoff[[i]]], {i, 1, Length[bcCoff]}];
   matG = 
    Table[Coefficient[
      cMatrix /. Thread[Cases[coff, Except[polyCoff[[i]]]] -> 0], 
      polyCoff[[i]]], {i, 1, Length[polyCoff]}];
   matF = 
    Table[Coefficient[cMatrix, bcCoff[[i]]*polyCoff[[j]]], {i, 1, 
      Length[bcCoff]}, {j, 1, Length[polyCoff]}];
   
   
   
   matOmegaH = 
    Join[Sequence @@ Table[matH[[i]], {i, 1, Length[bcCoff]}], 2];
   matOmegaG = 
    Join[Sequence @@ Table[matG[[j]], {j, 1, Length[polyCoff]}], 2];
   matGamma = 
    1/2 Join[
      Sequence @@ 
       Table[Join[
         Sequence @@ Table[matF[[i]][[j]], {j, 1, Length[polyCoff]}], 
         2], {i, 1, Length[bcCoff]}]];
   matM = 
    SparseArray[{Band[{1, Dimensions[matGamma][[1]] + 1}] -> matGamma,
       Band[{Dimensions[matGamma][[1]] + 1, 1}] -> 
       Transpose[matGamma]}, Plus @@ Dimensions[matGamma] {1, 1}];
   
   
   
   matI = IdentityMatrix[Length[cMatrix]];
   matKronecker = 
    Join[KroneckerProduct[bcCoff, matI], 
     KroneckerProduct[polyCoff, matI]];
   
   If[verbose, 
    Print["\!\(\*SubscriptBox[\(B\), \(M\)]\)(\[Lambda],a,s)=", 
     Transpose[matKronecker] . matM . matKronecker + 
       Join[matOmegaH, matOmegaG, 2] . matKronecker + matC // 
      MatrixForm]];
   
   
   {eigenValues, eigenVectors} = Eigensystem[matM // Normal];
   matD = DiagonalMatrix[eigenValues];
   matV = Normalize /@ eigenVectors;
   matDPlus = Replace[matD, _?Negative -> 0, {-1}];
   matDMinus = matDPlus - matD;
   matM1 = Chop[Transpose[matV] . matDPlus . matV];
   matM2 = Chop[Transpose[matV] . matDMinus . matV];
   
   BMI2 = Transpose[matKronecker] . matM2 . matKronecker;
   
   If[verbose, 
    Print["\!\(\*TemplateBox[{\"B\", \"M\", \"+\"},\"Subsuperscript\"]\)(\[Lambda],a,s)=", 
     Transpose[matKronecker] . matM1 . matKronecker + 
       Join[matOmegaH, matOmegaG, 2] . matKronecker + matC // 
      MatrixForm]];
   If[verbose, 
    Print["\!\(\*TemplateBox[{\"B\", \"M\", \"-\"},\"Subsuperscript\"]\)(\[Lambda],a,s)=", 
     Transpose[matKronecker] . matM2 . matKronecker // MatrixForm]];
   
   zCoff = Join[bcCoff, polyCoff];
   If[dcstatus == False,
    zkCoff = Table[Subscript[z, i], {i, 1, Length[zCoff]}];
    SDPVars = zCoff;
    BMI2Rules = Thread[zCoff -> zkCoff]; dcstatus = True,
    zkCoff = 
     Table[Subscript[z, 
      i], {i, Length[SDPVars] + 1, 
       Length[SDPVars] + Length[Complement[zCoff, SDPVars]]}];
    BMI2Rules = 
     Join[BMI2Rules, Thread[Complement[zCoff, SDPVars] -> zkCoff]];
    SDPVars = Join[SDPVars, Complement[zCoff, SDPVars]];
    ];
   
   If[matM2 == Table[Table[0, {Length[matM2]}], {Length[matM2]}], 
    AppendTo[LMISet, cMatrix]; Continue[]];
   
   matN = Chop[Transpose[matV] . MatrixPower[matDPlus, 1/2] . matV];
   
   
   matKronecker = KroneckerProduct[zCoff, matI];
   matNzI = matN . matKronecker;
   
   matLinear = 
    Join[matOmegaH, matOmegaG, 2] . matKronecker + matC;
   
   
   
   dBMI2 = (zCoff - (zCoff /. BMI2Rules)) . ((D[BMI2, #] & /@ 
         zCoff) /. BMI2Rules);
   
   
   matCorner = matLinear - (BMI2 /. BMI2Rules) - dBMI2;
   matCornerUT1 = UpperTriangularize[matCorner];
   matCornerUT2 = UpperTriangularize[matCorner, 1];
   matCorner = matCornerUT1 + Transpose[matCornerUT2];
   LMIConstraint = 
    Join[Join[-IdentityMatrix[Length[zCoff]*Length[cMatrix]], matNzI, 
      2], Join[Transpose[matNzI], matCorner, 2]];
   
   
   AppendTo[LMISet, LMIConstraint];
   ];
  
  If[verbose, Print["LMI constraints:\n", SparseArray /@ LMISet];
   Print["LMI variables:\n", SDPVars];
   Print["Variable correspondence:\n", BMI2Rules]];
  
  
  
  
  optimumSequence = {};
  initialVector = 
   Initial[cMatrixSet, SDPVars, dcpositiveCoff, dcsigmaCoff, 
    dcpolyCoff, paraRange, verbose, False, initialVector1];
  optimum = Thread[(SDPVars /. BMI2Rules) -> (initialVector)];
  If[verbose, 
   Print["Initial feasible solution:\n\!\(\*SuperscriptBox[\(z\), \(0\)]\)=", 
    Map[# /. # /; #[[1]] === (\[Lambda] /. BMI2Rules) :> 
        Style[#, Bold] &, optimum]]];
  AppendTo[optimumSequence, optimum];
  If[verbose, 
   Print["DC-initialVector: ", Thread[SDPVars -> (initialVector)]]];
  point = Thread[SDPVars -> (initialVector)];
  
  
  LMIConstraint = -Join[{Prepend[SDPVars - (SDPVars /. BMI2Rules), 
       2 \[Zeta]/\[Delta]]}, 
     Join[List /@ (SDPVars - (SDPVars /. BMI2Rules)), 
      IdentityMatrix[Length[SDPVars]], 2]];
  
  
  AppendTo[SDPVars, \[Zeta]];
  AppendTo[BMI2Rules, \[Zeta] -> zz];
  
  If[verbose, Print["LMI variables:\n", SDPVars]; 
   Print["Variable correspondence:\n", BMI2Rules]];
  
  
  
  k = 1;
  While[((\[Lambda] /. BMI2Rules) /. optimum) < -10^-5 && k <= round,
   SDPVars = DeleteDuplicates[Flatten[SDPVars]];
   paraRegion = 
    Cuboid[Table[paraRange[[1]], Length[SDPVars] - 1], 
     Table[paraRange[[2]], Length[SDPVars] - 1]];
   If[verbose, 
    Print["eigenvalues: LMISet/.\!\(\*SuperscriptBox[\(z\), \(k\)]\)=", 
     Table[Max[Eigenvalues[(LMISet /. optimum /. point)[[i]]]], {i, 1,
        Length[LMISet]}]]; 
    Print["eigenvalues: cMatrix/.\!\(\*SuperscriptBox[\(z\), \(k\)]\)=", 
     Table[Max[Eigenvalues[(cMatrixSet /. point)[[i]]]], {i, 1, 
       Length[cMatrixSet]}]]];
   
   {point, maximum} = 
    safeSemidefiniteOptimization[-\[Lambda] - \[Zeta], 
     (LMISet /. optimum), {makeSemidefiniteConeConstraints[{(
          LMIConstraint /. optimum)}][[1]], 
      DeleteCases[SDPVars, \[Lambda]] \[Element] paraRegion}, SDPVars, 
     {"PrimalMinimizerRules", "PrimalMinimumValue"}];
   maximum = -maximum;
   If[maximum === -Infinity, 
    If[verbose, 
     Print["DC: SDP subproblem failed (nonconvex/infeasible)."]]; 
    Return[$Failed]];
   optimum = 
    Thread[(SDPVars /. BMI2Rules) -> (SDPVars /. point)];
   If[verbose, 
    Print["Feasible solution:\n", Superscript["z", k], "=", 
     Map[# /. # /; #[[1]] === (\[Lambda] /. BMI2Rules) :> 
         Style[#, Bold] &, optimum]];
    Print["Maximum:\n", Superscript["(\[Lambda]+\[Zeta])", k], "=", 
     maximum]];
   AppendTo[optimumSequence, optimum];
   solutionDist = 
    Norm[Drop[((SDPVars /. 
           BMI2Rules) /. (optimumSequence[[-1]])) - ((SDPVars /. 
           BMI2Rules) /. (optimumSequence[[-2]])), -1]];
   If[verbose, 
    Print["|", Superscript["z", k], "-", Superscript["z", k - 1], 
     "|=", solutionDist]];
   
   If[solutionDist <= \[Epsilon]DC,
    Print["Close enough solutions: ", solutionDist, 
     " \[LessEqual] \[Epsilon]DC = ", \[Epsilon]DC];
    Break[]];
   k++;
   ];
  
  
  If[k > round, 
   If[verbose, 
    Print["DC: Maximum no.", round, " of iterations reached"]], 
   If[verbose, Print["DC: Found at round: ", k]]];
  DCTime = TimeUsed[] - DCTime;
  If[verbose, Print["DC-time elapsed: ", DCTime, "s"]];
  If[verbose, 
   Print["DC-optimum: ", 
    Thread[SDPVars -> (SDPVars /. BMI2Rules /. optimum)]]];
  Return[Thread[SDPVars -> (SDPVars /. BMI2Rules /. optimum)]];
  ]



AD[cMatrixSet_, bcCoff_, positiveCoff_, sigmaCoff_, polyCoff_, paraRange_, \[Epsilon]AD_, round_, verbose_, initialVector1_ : Automatic] := 
  Module[{ADtime, SDPVars, SDPVars1, SDPVars2, SDPVars1Rule, SDPVars2Rule, initialRules, paraRegion, point, maximum, optimumSequence, k, solutionDist},
   ADtime = TimeUsed[];
   SDPVars = DeleteDuplicates[Flatten[Join[sigmaCoff, polyCoff, bcCoff]]];
   SDPVars1 = DeleteDuplicates[Flatten[DeleteCases[Join[sigmaCoff, polyCoff], \[Lambda]]]];
   SDPVars2 = DeleteDuplicates[Flatten[bcCoff]];
   initialRules = 
    Thread[SDPVars -> 
      Initial[cMatrixSet, SDPVars, positiveCoff, sigmaCoff, polyCoff, 
       paraRange, verbose, True, initialVector1]];
   SDPVars1Rule = Thread[SDPVars1 -> (SDPVars1 /. initialRules)];
   If[verbose, Print["ramdom initial SDPVars1Rule=", SDPVars1Rule]];
   paraRegion = 
    Cuboid[Table[paraRange[[1]], Length[SDPVars2]], 
     Table[paraRange[[2]], Length[SDPVars2]]];
   {point, maximum} = 
    safeSemidefiniteOptimization[-\[Lambda], (cMatrixSet /. SDPVars1Rule),
     {SDPVars2 \[Element] paraRegion}, Append[SDPVars2, \[Lambda]], 
    {"PrimalMinimizerRules", "PrimalMinimumValue"}];
   If[maximum === Infinity, 
    If[verbose, 
     Print["AD: initial SDP subproblem failed (nonconvex/infeasible)."]];
    Return[$Failed]];
   SDPVars2Rule = Thread[SDPVars2 -> (SDPVars2 /. point)];
   If[verbose, Print["initial \[Lambda]=", -maximum]; 
    Print["eigenvalues: cMatrix/.\!\(\*SuperscriptBox[\(z\), \(0\)]\)=", 
     Table[Max[
       Eigenvalues[(cMatrixSet /. SDPVars1Rule /. point)[[i]]]], {i, 
       1, Length[cMatrixSet]}]];
    Print["AD-SDPVars1Rule:", SDPVars1Rule];
    Print["AD-SDPVars2Rule:", SDPVars2Rule];];
   optimumSequence = {};
   AppendTo[optimumSequence, 
    Join[SDPVars1Rule, SDPVars2Rule]];
   AppendTo[optimumSequence, 
    Join[SDPVars1Rule, SDPVars2Rule]];
   k = 1;
   
   While[k <= round ,
    
    
    If[verbose, Print[k, "th round optimizing SDPVars1"]];
    paraRegion = 
     Cuboid[Table[paraRange[[1]], Length[SDPVars1]], 
      Table[paraRange[[2]], Length[SDPVars1]]];
    {point, maximum} = 
     safeSemidefiniteOptimization[-\[Lambda], (cMatrixSet /. SDPVars2Rule),
       {SDPVars1 \[Element] paraRegion}, Append[SDPVars1, \[Lambda]], 
      {"PrimalMinimizerRules", "PrimalMinimumValue"}];
    If[maximum === Infinity, 
     If[verbose, 
      Print[
       "AD: SDPVars1 subproblem failed (nonconvex/infeasible)."]]; 
     Return[$Failed]];
    SDPVars1Rule = Thread[SDPVars1 -> (SDPVars1 /. point)];
    If[-maximum > -10^-5, Break[]];
    If[verbose, 
     Print["\[Lambda]=", -maximum, 
      ", eigenvalues: cMatrix/.\!\(\*SuperscriptBox[\(z\), \(k\)]\)=",
       Table[Max[
        Eigenvalues[(cMatrixSet /. point /. SDPVars2Rule)[[i]]]], {i, 
        1, Length[cMatrixSet]}]]];
    
    
    
    If[verbose, Print[k, "th round optimizing SDPVars2"]];
    paraRegion = 
     Cuboid[Table[paraRange[[1]], Length[SDPVars2]], 
      Table[paraRange[[2]], Length[SDPVars2]]];
    {point, maximum} = 
     safeSemidefiniteOptimization[-\[Lambda], (cMatrixSet /. SDPVars1Rule),
       {SDPVars2 \[Element] paraRegion}, Append[SDPVars2, \[Lambda]], 
      {"PrimalMinimizerRules", "PrimalMinimumValue"}];
    If[maximum === Infinity, 
     If[verbose, 
      Print[
       "AD: SDPVars2 subproblem failed (nonconvex/infeasible)."]]; 
     Return[$Failed]];
    SDPVars2Rule = Thread[SDPVars2 -> (SDPVars2 /. point)];
    If[-maximum > -10^-5, Break[]];
    If[verbose, 
     Print["\[Lambda]=", -maximum, 
      ", eigenvalues: cMatrix/.\!\(\*SuperscriptBox[\(z\), \(k\)]\)=",
       Table[Max[
        Eigenvalues[(cMatrixSet /. SDPVars1Rule /. point)[[i]]]], {i, 
        1, Length[cMatrixSet]}]]];
    
    optimumSequence[[2]] = Join[SDPVars1Rule, SDPVars2Rule];
    solutionDist = 
     Norm[((DeleteCases[
           SDPVars, \[Lambda]]) /. (optimumSequence[[1]])) - (((DeleteCases[SDPVars, \[Lambda]])) /. (optimumSequence[[2]]))];
    If[verbose, 
     Print["|", Superscript["z", k], "-", Superscript["z", k - 1], 
      "|=", solutionDist]];
    
    If[solutionDist <= \[Epsilon]AD,
     If[verbose, 
      Print["Close enough solutions: ", solutionDist, 
       " \[LessEqual] \[Epsilon]AD = ", \[Epsilon]AD]];
     Break[]];
    optimumSequence[[1]] = Join[SDPVars1Rule, SDPVars2Rule];
    k++;
    ];
   If[k > round, 
    If[verbose, 
     Print["AD: Maximum no. of iterations ", round " reached"]], 
    If[verbose, Print["AD: Found at round: ", k]]];
   ADtime = TimeUsed[] - ADtime;
   If[verbose, Print["AD-time elapsed: ", ADtime, "s"]];
   If[verbose, 
    Print["AD-optimum: ", Join[SDPVars1Rule, SDPVars2Rule]]];
   Return[Join[SDPVars1Rule, SDPVars2Rule]];
   ];



ExponentialCon[varSet_, flowVec_, LieOrder_, bcTemp_, rank_, 
   initialineq_, initialeq_, unsafeineq_, unsafeeq_, domineq_, domeq_,
    paraRange_, LieSequence_, cMatrixSet_, 
   polyAddDegree_, \[Epsilon]L_, verbose_] := 
  Module[{ExTime, cMatrixSet1, \[Sigma]W, polyTargetDegree, sosdegree, polydegree, LieConstraints, degree, basis, cMatrix, SDPVars, paraRegion, point, maximum, cSet, cInitial, bcCandidate, bcCoffMax, bcCoff, bcTempCoff, verifiedLie, verifiedUnsafe, verifiedInitial},
   
   ExTime = TimeUsed[];
   
   cMatrixSet1 = cMatrixSet;
   For[i = 1, i <= LieOrder, i++, cMatrixSet1 = Drop[cMatrixSet1, -1];
     If[Length[domineq] > 0, 
     cMatrixSet1 = 
      Drop[cMatrixSet1, {Length[initialineq] + Length[unsafeineq] + 1,
         Length[initialineq] + Length[unsafeineq] + Length[domineq]}]];
    ];
   
   
   If[Length[domineq] + Length[domeq] > 0,
    polyTargetDegree = 
     degreeDecision[polyDegree[LieSequence[[2]], varSet], 0, domineq, 
      domeq, varSet];
    If[Length[polyTargetDegree] == 0, Print["No domain!"]];
    sosdegree = 
     Table[polyTargetDegree[[i]], {i, 1, Length[domineq]}];
    polydegree = 
     Table[polyTargetDegree[[Length[domineq] + i]], {i, 1, 
       Length[domeq]}];
    If[verbose, 
     Print["domain sosdegree=", sosdegree, "  domain polydegree=", 
      polydegree]];
    ];
   
   
   \[Sigma]W = 
    Table[polyTemp[varSet, identifier[{w, j}], sosdegree[[j]]], {j, 1,
       Length[domineq]}];
   LieConstraints = -LieSequence[[2]] - c*LieSequence[[1]] - 
     Sum[\[Sigma]W[[j]]*domineq[[j]], {j, 1, Length[domineq]}] + 
     Sum[polyTemp[varSet, identifier[{y, j}], polydegree[[j]]]*
       domeq[[j]], {j, 1, Length[domeq]}] - \[Epsilon]L;
   If[verbose, 
    Print["\[Sigma]W=", \[Sigma]W, ", LieConstraints=", 
     LieConstraints]];
   
   
   
   For[i = 1, i <= Length[domineq], i++,
    degree = Ceiling[polyDegreeMax[\[Sigma]W[[i]], varSet]/2];
    basis = 
     monomList[varSet, 
      degree];
    cMatrix = 
     coefficientMatrix[varSet, 
      basis, \[Sigma]W[[i]]];
    If[verbose, 
     Print["\[Sigma]W[[i]] with basis=", basis, " of degree=", 
      polyDegree[\[Sigma]W[[i]], varSet], 
      ":\nF(a,s)=", -cMatrix // MatrixForm]];
    cMatrix = -cMatrix + \[Lambda]*IdentityMatrix[Length[cMatrix]];
    AppendTo[cMatrixSet1, cMatrix];
    ];
   
   degree = Ceiling[polyDegreeMax[LieConstraints, varSet]/2];
   basis = 
    monomList[varSet, 
     degree];
   cMatrix = 
    coefficientMatrix[varSet, basis, 
     LieConstraints];
   If[verbose, 
    Print["LieConstraints with basis=", basis, " of degree=", polyDegree[LieConstraints, varSet], ":\nF(a,s)=", -cMatrix // MatrixForm]];
   cMatrix = -cMatrix + \[Lambda]*IdentityMatrix[Length[cMatrix]];
   AppendTo[cMatrixSet1, cMatrix];
   
   
   For[i = 1, i <= Length[cMatrixSet1], i++,
    If[i == 1, SDPVars = Variables[cMatrixSet1[[i]]], 
      SDPVars = 
       DeleteDuplicates[Join[SDPVars, Variables[cMatrixSet1[[i]]]]]];
    ];
   If[verbose, Print["cMatrixSet1=", cMatrixSet1 // MatrixForm]];
   
   bcCoff = Cases[SDPVars, Subscript[a, _]];
   SDPVars = DeleteCases[SDPVars, c];
   cSet = {1, 0.5, 0, -0.5, -1};
   For[i = 1, i <= Length[cSet], i++,
    cInitial = {c -> cSet[[i]]};
    If[verbose, Print["cInitial=", cInitial]];
    paraRegion = 
     Cuboid[Table[paraRange[[1]], Length[SDPVars] - 1], 
      Table[paraRange[[2]], Length[SDPVars] - 1]];
   {point, maximum} = 
    safeSemidefiniteOptimization[-\[Lambda], (cMatrixSet1 /. cInitial), 
     {DeleteCases[SDPVars, \[Lambda]] \[Element] paraRegion}, SDPVars, 
     {"PrimalMinimizerRules", "PrimalMinimumValue"}];
    maximum = -maximum;
    If[verbose, 
     Print["\[Lambda]=", maximum, ", eigenvalues: cMatrix/.point=", 
      Table[Max[
        Eigenvalues[(cMatrixSet1[[i]] /. cInitial) /. point]], {i, 1, 
        Length[cMatrixSet1]}]]];
    bcCandidate = bcTemp /. point;
    If[verbose, 
     Print["ExponentialCon: Barrier certificate candidate:", 
      bcCandidate]];
    bcCoffMax = safeCoeffScale[bcCoff /. point];
    bcTempCoff = ((bcCoff /. point)/bcCoffMax) /. 
      x_ /; Abs[x] <= 10^-5 -> 0;
    bcTempCoff = bcTempCoff*bcCoffMax;
    bcCandidate = bcTemp /. (Thread[bcCoff -> bcTempCoff]);
    If[verbose, 
     Print["After estimating, bcCandidate=", bcCandidate]];
    
    {verifiedLie, verifiedUnsafe, verifiedInitial} = 
     Vertification[varSet, LieOrder, rank, flowVec, initialineq, 
      initialeq, unsafeineq, unsafeeq, bcCandidate, domineq, domeq, 
      point, verbose];
    If[verifiedLie && verifiedUnsafe && verifiedInitial, 
     If[verbose, Print["ExponentialCon-verification: True!"]]; 
     Break[], 
     If[verbose, Print["ExponentialCon-verification: False!"]]];
    ];
   ExTime = TimeUsed[] - ExTime;
   If[verbose, Print["Ex-time elapsed: ", ExTime, "s"]];
   Return[verifiedLie && verifiedUnsafe && verifiedInitial];
   ];


InterDC[varSet_, flowVec_, bcTemp_, LieOrder_, initialineq_, 
   initialeq_, unsafeineq_, unsafeeq_, domineq_, domeq_, paraRange_, 
   LieSequence_, cMatrixSet_, polyAddDegree_, inter\[Epsilon]I_, 
   inter\[Epsilon]U_, \[Epsilon]L_, \[Epsilon]DC_, \[Delta]_, 
   verbose_, interDegree1_ : Automatic] := 
  Module[{interDegree, InterDCTime, interDCTemp, sosSet, sosConstraint, cMatrixSet1, cMatrixSet2, \[Sigma]I, \[Sigma]U, \[Sigma]W, LieConstraints, polyTargetDegree, sosdegree, polydegree, basis, degree, cMatrix, domConstraint, InitialConstraint, UnsafeConstraint, domainRange, domMin, domMax, ranges, interCoff, interpolyVar, interCoffRule, target, SDPVars, paraRegion, point, point1, point2, minimum, interDCinitial, dcsigmaCoff, dcpolyCoff},
   InterDCTime = TimeUsed[];
   
   
   
   If[interDegree1 === Automatic, 
    interDegree = 
     polyAddDegree + polyDegree[LieSequence[[2]], varSet] - 
      polyDegree[LieSequence[[1]], varSet], 
    interDegree = interDegree1];
   interDCTemp = polyTemp[varSet, b, interDegree];
   
   Print["interDegree=", interDegree, 
    "   Template Interopolation-DC polynomial: \n", interDCTemp];
   sosSet = {};
   
   polyTargetDegree = 
    degreeDecision[interDegree, polyAddDegree, initialineq, initialeq,
      varSet];
   If[Length[polyTargetDegree] == 0, 
    Print["I: interDCDegree is a Wrong Degree!"]; Return[];];
   sosdegree = 
    Table[polyTargetDegree[[i]], {i, 1, Length[initialineq]}];
   polydegree = 
    Table[polyTargetDegree[[Length[initialineq] + i]], {i, 1, 
      Length[initialeq]}];
   If[verbose, 
    Print["initial sosdegree=", sosdegree, ",  initial polydegree=", 
     polydegree]];
   \[Sigma]I = 
    Table[polyTemp[varSet, identifier[{c, i}], sosdegree[[i]]], {i, 1,
       Length[initialineq]}];
   If[Length[initialineq] > 0 || Length[initialeq] > 0, 
    AppendTo[
     sosSet, -interDCTemp - inter\[Epsilon]I - 
      Sum[\[Sigma]I[[i]]*initialineq[[i]], {i, 1, 
        Length[initialineq]}] + 
      Sum[polyTemp[varSet, identifier[{d, i}], polydegree[[i]]]*
        initialeq[[i]], {i, 1, Length[initialeq]}]]];
   
   
   
   polyTargetDegree = 
    degreeDecision[interDegree, polyAddDegree, unsafeineq, unsafeeq, 
     varSet];
   If[Length[polyTargetDegree] == 0, 
    Print["U: interDCDegree is a Wrong Degree!"]; Return[];];
   sosdegree = 
    Table[polyTargetDegree[[i]], {i, 1, Length[unsafeineq]}];
   polydegree = 
    Table[polyTargetDegree[[Length[unsafeineq] + i]], {i, 1, 
      Length[unsafeeq]}];
   If[verbose, 
    Print["unsafe sosdegree=", sosdegree, "  unsafe polydegree=", 
     polydegree]];
   \[Sigma]U = 
    Table[polyTemp[varSet, identifier[{e, i}], sosdegree[[i]]], {i, 1,
       Length[unsafeineq]}];
   If[Length[unsafeineq] > 0 || Length[unsafeeq] > 0, 
    AppendTo[sosSet, 
     interDCTemp - inter\[Epsilon]U - 
      Sum[\[Sigma]U[[i]]*unsafeineq[[i]], {i, 1, 
        Length[unsafeineq]}] + 
      Sum[polyTemp[varSet, identifier[{f, i}], polydegree[[i]]]*
        unsafeeq[[i]], {i, 1, Length[unsafeeq]}]]];
   sosSet = 
    Map[Collect[#, varSet, Simplify] &, 
     Join[\[Sigma]I, \[Sigma]U, sosSet]];
   If[verbose, Print["SOS constraints:\n", sosSet]];
   
   
   cMatrixSet1 = {};
   For[n = 1, n <= Length[sosSet], n++,
    sosConstraint = sosSet[[n]];
    degree = Ceiling[polyDegreeMax[sosConstraint, varSet]/2];
    basis = 
     monomList[varSet, 
      degree];
    cMatrix = 
     coefficientMatrix[varSet, basis, 
      sosConstraint];
    If[verbose, 
     Print[n, "th constraint with basis=", basis, " of degree=", 
      polyDegree[sosConstraint, varSet], 
      ":\nF(a,s)=", -cMatrix // MatrixForm]];
    cMatrix = -cMatrix;
    If[n == 1, SDPVars = Variables[cMatrix], 
     SDPVars = DeleteDuplicates[Join[SDPVars, Variables[cMatrix]]]];
    AppendTo[cMatrixSet1, cMatrix];
    ];
   
   
   
   If[Length[domineq] + Length[domeq] > 0,
    domConstraint = 
     Join[Table[domineq[[i]] >= 0, {i, 1, Length[domineq]}], 
      Table[domeq[[i]] == 0, {i, 1, Length[domeq]}]];
    domainRange = {};
    For[i = 1, i <= Length[varSet], i++,
     domMin = Minimize[{varSet[[i]], domConstraint}, varSet][[1]];
     domMax = Maximize[{varSet[[i]], domConstraint}, varSet][[1]];
     AppendTo[domainRange, {domMin, domMax}];
     ],
    InitialConstraint = 
     Join[Table[initialineq[[i]] >= 0, {i, 1, Length[initialineq]}], 
      Table[initialeq[[i]] == 0, {i, 1, Length[initialeq]}]];
    UnsafeConstraint = 
     Join[Table[unsafeineq[[i]] >= 0, {i, 1, Length[unsafeineq]}], 
      Table[unsafeeq[[i]] == 0, {i, 1, Length[unsafeeq]}]];
    domainRange = {};
    For[i = 1, i <= Length[varSet], i++,
     domMin = 
      Min[Minimize[{varSet[[i]], InitialConstraint}, varSet][[1]], 
       Minimize[{varSet[[i]], UnsafeConstraint}, varSet][[1]]];
     domMax = 
      Max[Maximize[{varSet[[i]], InitialConstraint}, varSet][[1]], 
       Maximize[{varSet[[i]], UnsafeConstraint}, varSet][[1]]];
     AppendTo[domainRange, {domMin, domMax}];
     ]
    ];
   ranges = 
    Table[Prepend[domainRange[[i]], varSet[[i]]], {i, 1, 
      Length[varSet]}];
   Print["ranges D=", ranges];
   ranges = Sequence @@ ranges;
   interCoff = 
    Variables[interDCTemp /. Thread[varSet -> 1]];
   interpolyVar = {};
   For[i = 1, i <= Length[interCoff], i++,
    interCoffRule = 
     Join[{interCoff[[i]] -> 1}, 
      Thread[DeleteCases[interCoff, interCoff[[i]]] -> 0]];
    AppendTo[interpolyVar, interDCTemp /. interCoffRule];
    ];
   Print["interpolyVar=", interpolyVar];
   target = 
    Thread[Integrate[interpolyVar, Evaluate[ranges]]] . interCoff;
   Print["the target=", target];
   
   
   
   paraRegion = 
    Cuboid[Table[paraRange[[1]], Length[SDPVars]], 
     Table[paraRange[[2]], Length[SDPVars]]];
  {point1, minimum} = 
   safeSemidefiniteOptimization[target, cMatrixSet1, 
    {SDPVars \[Element] paraRegion}, SDPVars, {"PrimalMinimizerRules", 
     "PrimalMinimumValue"}, MaxIterations -> 200];
   Print["minimum target=", minimum, ", eigenvalues: cMatrix/.point=",
     Table[Max[Eigenvalues[cMatrixSet1[[i]] /. point1]], {i, 1, 
      Length[cMatrixSet1]}]];
   Print["the interopolation polynomial1=", interCoff /. point1];
  {point2, minimum} = 
   safeSemidefiniteOptimization[-target, cMatrixSet1, 
    {SDPVars \[Element] paraRegion}, SDPVars, {"PrimalMinimizerRules", 
     "PrimalMinimumValue"}, MaxIterations -> 200];
   Print["maximum target=", -minimum, 
    ", eigenvalues: cMatrix/.point=", 
    Table[Max[Eigenvalues[cMatrixSet1[[i]] /. point2]], {i, 1, 
      Length[cMatrixSet1]}]];
   Print["the interopolation polynomial2=", interCoff /. point2];
   interDCinitial = 
    Thread[interCoff -> 
      0.5*((interCoff /. point1) + (interCoff /. point2))];
   Print["the interDCinitial=", interDCinitial];
   
   
   
   
   
   cMatrixSet2 = cMatrixSet;
   For[i = 1, i <= LieOrder, i++, cMatrixSet2 = Drop[cMatrixSet2, -1];
     If[Length[domineq] > 0, 
     cMatrixSet2 = 
      Drop[cMatrixSet2, {Length[initialineq] + Length[unsafeineq] + 1,
         Length[initialineq] + Length[unsafeineq] + Length[domineq]}]];
    ];
   
   
   If[Length[domineq] + Length[domeq] > 0,
    polyTargetDegree = 
     degreeDecision[
      Max[Thread[
        polyDegree[{LieSequence[[2]], interDCTemp*LieSequence[[1]]}, 
         varSet]]], polyAddDegree, domineq, domeq, varSet];
    If[Length[polyTargetDegree] == 0, 
     Print["LieDegree is a Wrong Degree!"]; Return[];];
    sosdegree = 
     Table[polyTargetDegree[[i]], {i, 1, Length[domineq]}];
    polydegree = 
     Table[polyTargetDegree[[Length[domineq] + i]], {i, 1, 
       Length[domeq]}];
    If[verbose, 
     Print["domain sosdegree=", sosdegree, "  domain polydegree=", 
      polydegree]];
    ];
   
   
   \[Sigma]W = 
    Table[polyTemp[varSet, identifier[{w, j}], sosdegree[[j]]], {j, 1,
       Length[domineq]}];
   LieConstraints = -LieSequence[[2]] + interDCTemp*LieSequence[[1]] -
      Sum[\[Sigma]W[[j]]*domineq[[j]], {j, 1, Length[domineq]}] + 
     Sum[polyTemp[varSet, identifier[{y, j}], polydegree[[j]]]*
       domeq[[j]], {j, 1, Length[domeq]}] - \[Epsilon]L;
   
   
   
   
   
   
   For[i = 1, i <= Length[initialineq], i++, 
    cMatrixSet2 = 
     Insert[cMatrixSet2, 
      cMatrixSet1[[i]] + \[Lambda]*
        IdentityMatrix[Length[cMatrixSet1[[i]]]], 
      Length[initialineq] + i]];
   
   For[i = 1, i <= Length[unsafeineq], i++, 
    cMatrixSet2 = 
     Insert[cMatrixSet2, 
      cMatrixSet1[[Length[initialineq] + i]] + \[Lambda]*
        IdentityMatrix[
         Length[cMatrixSet1[[Length[initialineq] + i]]]], 
      2*Length[initialineq] + Length[unsafeineq] + i]];
   
   
   
   For[i = 1, i <= Length[domineq], i++,
    degree = Ceiling[polyDegreeMax[\[Sigma]W[[i]], varSet]/2];
    basis = monomList[varSet, degree];
    cMatrix = coefficientMatrix[varSet, basis, \[Sigma]W[[i]]];
    If[verbose, 
     Print["\[Sigma]W[[i]] with basis=", basis, " of degree=", 
      polyDegree[\[Sigma]W[[i]], varSet], 
      ":\nF(a,s)=", -cMatrix // MatrixForm]];
    cMatrix = -cMatrix + \[Lambda]*IdentityMatrix[Length[cMatrix]];
    cMatrixSet2 = 
     Insert[cMatrixSet2, cMatrix, 
      2*Length[initialineq] + 2*Length[unsafeineq] + i];
    ];
   
   
   
   cMatrixSet2 = 
    Insert[cMatrixSet2, 
     cMatrixSet1[[Length[initialineq] + Length[unsafeineq] + 
         1]] + \[Lambda]*
       IdentityMatrix[
        Length[cMatrixSet1[[Length[initialineq] + 
            Length[unsafeineq] + 1]]]], 
     2*Length[initialineq] + 2*Length[unsafeineq] + Length[domineq] + 
      2];
   cMatrixSet2 = 
    Insert[cMatrixSet2, 
     cMatrixSet1[[Length[initialineq] + Length[unsafeineq] + 
         2]] + \[Lambda]*
       IdentityMatrix[
        Length[cMatrixSet1[[Length[initialineq] + 
            Length[unsafeineq] + 2]]]], 
     2*Length[initialineq] + 2*Length[unsafeineq] + Length[domineq] + 
      4];
   
   
   
   degree = Ceiling[polyDegreeMax[LieConstraints, varSet]/2];
   basis = monomList[varSet, degree];
   cMatrix = coefficientMatrix[varSet, basis, LieConstraints];
   If[verbose, 
    Print["LieConstraints with basis=", basis, " of degree=", 
     polyDegree[LieConstraints, varSet], 
     ":\nF(a,s)=", -cMatrix // MatrixForm]];
   cMatrix = -cMatrix + \[Lambda]*IdentityMatrix[Length[cMatrix]];
   AppendTo[cMatrixSet2, cMatrix];
   
   
   For[i = 1, i <= Length[cMatrixSet2], i++,
    If[i == 1, SDPVars = Variables[cMatrixSet2[[i]]], 
      SDPVars = 
       DeleteDuplicates[Join[SDPVars, Variables[cMatrixSet2[[i]]]]]];
    ];
   
   
   dcsigmaCoff = 
    Join[{\[Lambda]}, 
     Join @@ Table[
       Cases[SDPVars, 
        Subscript[ToExpression[StringJoin[ToString /@ {r, i}]], 
         Row[_]]], {i, 1, Length[initialineq]}], 
     Join @@ Table[
       Cases[SDPVars, 
        Subscript[ToExpression[StringJoin[ToString /@ {c, i}]], 
         Row[_]]], {i, 1, Length[initialineq]}], 
     Join @@ Table[
       Cases[SDPVars, 
        Subscript[ToExpression[StringJoin[ToString /@ {s, i}]], 
         Row[_]]], {i, 1, Length[initialeq]}],
     Join @@ 
      Table[Cases[SDPVars, 
        Subscript[ToExpression[StringJoin[ToString /@ {d, i}]], 
         Row[_]]], {i, 1, Length[initialeq]}], 
     Join @@ Table[
       Cases[SDPVars, 
        Subscript[ToExpression[StringJoin[ToString /@ {t, i}]], 
         Row[_]]], {i, 1, Length[unsafeineq]}], 
     Join @@ Table[
       Cases[SDPVars, 
        Subscript[ToExpression[StringJoin[ToString /@ {e, i}]], 
         Row[_]]], {i, 1, Length[unsafeineq]}], 
     Join @@ Table[
       Cases[SDPVars, 
        Subscript[ToExpression[StringJoin[ToString /@ {u, i}]], 
         Row[_]]], {i, 1, Length[unsafeeq]}], 
     Join @@ Table[
       Cases[SDPVars, 
        Subscript[ToExpression[StringJoin[ToString /@ {f, i}]], 
         Row[_]]], {i, 1, Length[unsafeeq]}], 
     Join @@ Table[
       Cases[SDPVars, 
        Subscript[ToExpression[StringJoin[ToString /@ {w, j}]], 
         Row[_]]], {j, 1, Length[domineq]}], 
     Join @@ Table[
       Cases[SDPVars, 
        Subscript[ToExpression[StringJoin[ToString /@ {y, j}]], 
         Row[_]]], {j, 1, Length[domeq]}]];
   
   If[Verbose, Print["dcsigmaCoff=", dcsigmaCoff]];
   dcpolyCoff = interCoff;
   If[Verbose, Print["dcpolyCoff=", dcpolyCoff]];
   
   \[Epsilon]DC1 = 10^-4;
   point = 
    DC[varSet, flowVec, rank, domineq, domeq, initialineq, initialeq, 
     unsafeineq, unsafeeq, paraRange, 
     LieOrder, \[Epsilon]DC1, \[Delta], bcTemp, cMatrixSet2, 
     dcsigmaCoff, dcpolyCoff, verbose, interDCinitial];
   
   InterDCTime = TimeUsed[] - InterDCTime;
   Print["interopolation-time elapsed: ", InterDCTime, "s"];
   Return[point];
   ];


InterDCpart1[varSet_, flowVec_, initialineq_, initialeq_, unsafeineq_,
    unsafeeq_, domineq_, domeq_, paraRange_, LieSequence_, 
   polyAddDegree_, inter\[Epsilon]I_, inter\[Epsilon]U_, verbose_, 
   interDegree1_ : Automatic] := 
  Module[{interDegree, interDCTemp, sosSet, sosConstraint, cMatrixSet1, \[Sigma]I, \[Sigma]U, polyTargetDegree, sosdegree, polydegree, basis, degree, cMatrix, interCoff, SDPVars, paraRegion, point1, minimum, n, tmp, initIneq, initEq, unsafeIneq, unsafeEq},
   
   initIneq = initialineq;
   initEq = initialeq;
   unsafeIneq = unsafeineq;
   unsafeEq = unsafeeq;
   tmp = requireSingleComponent[initIneq, initEq, "InterDCpart1 initial"];
   If[tmp === $Failed, Return[$Failed]];
   {initIneq, initEq} = tmp;
   tmp = requireSingleComponent[unsafeIneq, unsafeEq, "InterDCpart1 unsafe"];
   If[tmp === $Failed, Return[$Failed]];
   {unsafeIneq, unsafeEq} = tmp;
   initIneq = DeleteCases[Flatten[initIneq, Infinity], {}];
   initEq = DeleteCases[Flatten[initEq, Infinity], {}];
   unsafeIneq = DeleteCases[Flatten[unsafeIneq, Infinity], {}];
   unsafeEq = DeleteCases[Flatten[unsafeEq, Infinity], {}];
   If[! ListQ[initIneq], initIneq = {initIneq}];
   If[! ListQ[initEq], initEq = {initEq}];
   If[! ListQ[unsafeIneq], unsafeIneq = {unsafeIneq}];
   If[! ListQ[unsafeEq], unsafeEq = {unsafeEq}];
   initIneq = Map[If[ListQ[#], First@Flatten[#], #] &, initIneq];
   initEq = Map[If[ListQ[#], First@Flatten[#], #] &, initEq];
   unsafeIneq = Map[If[ListQ[#], First@Flatten[#], #] &, unsafeIneq];
   unsafeEq = Map[If[ListQ[#], First@Flatten[#], #] &, unsafeEq];
   
   
   
   If[interDegree1 === Automatic, 
    interDegree = 
     polyDegree[LieSequence[[2]], varSet] - 
      polyDegree[LieSequence[[1]], varSet], 
    interDegree = interDegree1];
   interDCTemp = polyTemp[varSet, b, interDegree];
   interCoff = 
    Variables[interDCTemp /. Thread[varSet -> 1]];
   
   If[verbose, 
    Print["interDegree=", interDegree, 
     "   Template Interopolation-DC polynomial: \n", interDCTemp]];
   sosSet = {};
   
   polyTargetDegree = 
    degreeDecision[interDegree, polyAddDegree, initIneq, initEq,
      varSet];
   If[Length[polyTargetDegree] == 0, 
    Print["I: interDCDegree is a Wrong Degree!"]; Return[];];
   sosdegree = 
    Table[polyTargetDegree[[i]], {i, 1, Length[initIneq]}];
   polydegree = 
    Table[polyTargetDegree[[Length[initIneq] + i]], {i, 1, 
      Length[initEq]}];
   If[verbose, 
    Print["initial sosdegree=", sosdegree, ",  initial polydegree=", 
     polydegree]];
   \[Sigma]I = 
    Table[polyTemp[varSet, identifier[{c, i}], sosdegree[[i]]], {i, 1,
       Length[initIneq]}];
   If[Length[initIneq] > 0 || Length[initEq] > 0, 
    AppendTo[
     sosSet, -interDCTemp - \[Lambda] - 
      Sum[\[Sigma]I[[i]]*initIneq[[i]], {i, 1, 
        Length[initIneq]}] + 
      Sum[polyTemp[varSet, identifier[{d, i}], polydegree[[i]]]*
        initEq[[i]], {i, 1, Length[initEq]}]]];
   
   
   
   polyTargetDegree = 
    degreeDecision[interDegree, polyAddDegree, unsafeIneq, unsafeEq, 
     varSet];
   If[Length[polyTargetDegree] == 0, 
    Print["U: interDCDegree is a Wrong Degree!"]; Return[];];
   sosdegree = 
    Table[polyTargetDegree[[i]], {i, 1, Length[unsafeIneq]}];
   polydegree = 
    Table[polyTargetDegree[[Length[unsafeIneq] + i]], {i, 1, 
      Length[unsafeEq]}];
   If[verbose, 
    Print["unsafe sosdegree=", sosdegree, "  unsafe polydegree=", 
     polydegree]];
   \[Sigma]U = 
    Table[polyTemp[varSet, identifier[{e, i}], sosdegree[[i]]], {i, 1,
       Length[unsafeIneq]}];
   If[Length[unsafeIneq] > 0 || Length[unsafeEq] > 0, 
    AppendTo[sosSet, 
     interDCTemp - \[Lambda] - 
      Sum[\[Sigma]U[[i]]*unsafeIneq[[i]], {i, 1, 
        Length[unsafeIneq]}] + 
      Sum[polyTemp[varSet, identifier[{f, i}], polydegree[[i]]]*
        unsafeEq[[i]], {i, 1, Length[unsafeEq]}]]];
   sosSet = 
    Map[Collect[#, varSet, Simplify] &, 
     Join[\[Sigma]I, \[Sigma]U, sosSet]];
   If[verbose, Print["SOS constraints:\n", sosSet]];
   
   
   cMatrixSet1 = {};
   For[n = 1, n <= Length[sosSet], n++,
    sosConstraint = sosSet[[n]];
    degree = Ceiling[polyDegreeMax[sosConstraint, varSet]/2];
    basis = 
     monomList[varSet, 
      degree];
    cMatrix = 
     coefficientMatrix[varSet, basis, 
      sosConstraint];
    If[verbose, 
     Print[n, "th constraint with basis=", basis, " of degree=", 
      polyDegree[sosConstraint, varSet], 
      ":\nF(a,s)=", -cMatrix // MatrixForm]];
    cMatrix = -cMatrix;
    If[n == 1, SDPVars = Variables[cMatrix], 
     SDPVars = DeleteDuplicates[Join[SDPVars, Variables[cMatrix]]]];
    AppendTo[cMatrixSet1, Chop[cMatrix]];
    ];
   If[verbose, Print["cMatrix=", cMatrix // MatrixForm]];
   SDPVars = DeleteCases[SDPVars, \[Lambda]];
   
   
   
   paraRegion = 
    Cuboid[Table[paraRange[[1]], Length[SDPVars]], 
     Table[paraRange[[2]], Length[SDPVars]]];
  {point1, minimum} = 
   safeSemidefiniteOptimization[-\[Lambda], cMatrixSet1, 
    {SDPVars \[Element] paraRegion}, Join[SDPVars, {\[Lambda]}], 
    {"PrimalMinimizerRules", "PrimalMinimumValue"}, 
    MaxIterations -> 300];
   If[verbose, 
    Print["maximum target=", -minimum, 
     ", eigenvalues: cMatrix/.point=", 
     Table[Max[Eigenvalues[cMatrixSet1[[i]] /. point1]], {i, 1, 
       Length[cMatrixSet1]}]]];
   If[verbose, 
    Print["the interopolation polynomial1=", interCoff /. point1];
    renderGraphics2D[varSet, flowVec, interDCTemp /. point1, 
     initialineq, initialeq, unsafeineq, unsafeeq, domineq, domeq];];
   
   Return[{interCoff /. point1, interCoff /. point1}];
   ];





InterDC[varSet_, flowVec_, bcTemp_, LieOrder_, rank_, initialineq_, 
   initialeq_, unsafeineq_, unsafeeq_, domineq_, domeq_, paraRange_, 
   LieSequence_, cMatrixSet_, polyAddDegree_, inter\[Epsilon]I_, 
   inter\[Epsilon]U_, \[Epsilon]L_, \[Epsilon]interDC_, \[Delta]_, 
   interCoff1_, interCoff2_, verbose_, interDegree1_ : Automatic, 
   DCADJudge_, seed_] := 
  Module[{interDegree, InterDCTime, interDCTemp, cMatrixSet2, \[Sigma]W, LieConstraints, polyTargetDegree, sosdegree, polydegree, basis, degree, cMatrix, interCoff, SDPVars, point, interDCinitial, dcsigmaCoff, dcpolyCoff, DCround, DCverbose, ADround, ADverbose, cSet, bcCandidate, bcCoffMax, bcCoff, bcTempCoff, verifiedLie, verifiedUnsafe, verifiedInitial, positiveCoff, tmp, initIneq, initEq, unsafeIneq, unsafeEq, i, j},
   
   initIneq = initialineq;
   initEq = initialeq;
   unsafeIneq = unsafeineq;
   unsafeEq = unsafeeq;
   tmp = requireSingleComponent[initIneq, initEq, "InterDC initial"];
   If[tmp === $Failed, Return[$Failed]];
   {initIneq, initEq} = tmp;
   tmp = requireSingleComponent[unsafeIneq, unsafeEq, "InterDC unsafe"];
   If[tmp === $Failed, Return[$Failed]];
   {unsafeIneq, unsafeEq} = tmp;
   initIneq = DeleteCases[Flatten[initIneq, Infinity], {}];
   initEq = DeleteCases[Flatten[initEq, Infinity], {}];
   unsafeIneq = DeleteCases[Flatten[unsafeIneq, Infinity], {}];
   unsafeEq = DeleteCases[Flatten[unsafeEq, Infinity], {}];
   
   
   InterDCTime = TimeUsed[];
   If[interDegree1 === Automatic, 
    interDegree = 
     polyDegree[LieSequence[[2]], varSet] - 
      polyDegree[LieSequence[[1]], varSet], 
    interDegree = interDegree1];
   interDCTemp = polyTemp[varSet, b, interDegree];
   interCoff = 
    Variables[interDCTemp /. Thread[varSet -> 1]];
   If[verbose, 
    Print["c*(interCoff/.point1)+(1-c)*(interCoff/.point2)=", 
     c*(interCoff1) + (1 - c)*(interCoff2)]];
   
   If[verbose, Print["interDCTemp=", interDCTemp]];
   
   cMatrixSet2 = cMatrixSet;
   For[j = 1, j <= LieOrder, j++, cMatrixSet2 = Drop[cMatrixSet2, -1];
     If[Length[domineq] > 0, 
     cMatrixSet2 = 
      Drop[cMatrixSet2, {Length[initIneq] + Length[unsafeIneq] + 1,
         Length[initIneq] + Length[unsafeIneq] + Length[domineq]}]];
    ];
   
   
   If[Length[domineq] + Length[domeq] > 0,
    polyTargetDegree = 
     degreeDecision[
      Max[Thread[
        polyDegree[{LieSequence[[2]], interDCTemp*LieSequence[[1]]}, 
         varSet]]], 0, domineq, domeq, varSet];
    If[Length[polyTargetDegree] == 0, 
     Print["LieDegree is a Wrong Degree!"]; Return[];];
    sosdegree = 
     Table[polyTargetDegree[[j]], {j, 1, Length[domineq]}];
    polydegree = 
     Table[polyTargetDegree[[Length[domineq] + i]], {i, 1, 
       Length[domeq]}];
    If[verbose, 
     Print["domain sosdegree=", sosdegree, "  domain polydegree=", 
      polydegree]];
    ];
   
   
   \[Sigma]W = 
    Table[polyTemp[varSet, identifier[{w, j}], sosdegree[[j]]], {j, 1,
       Length[domineq]}];
   LieConstraints = -LieSequence[[2]] + interDCTemp*LieSequence[[1]] -
      Sum[\[Sigma]W[[j]]*domineq[[j]], {j, 1, Length[domineq]}] + 
     Sum[polyTemp[varSet, identifier[{y, j}], polydegree[[j]]]*
       domeq[[j]], {j, 1, Length[domeq]}] - \[Epsilon]L;
   LieConstraints = 
    Map[Collect[#, varSet, Simplify] &, LieConstraints];
   
   
   
   
   
   
   
   For[j = 1, j <= Length[domineq], j++,
    degree = Ceiling[polyDegreeMax[\[Sigma]W[[j]], varSet]/2];
    basis = monomList[varSet, degree];
    cMatrix = coefficientMatrix[varSet, basis, \[Sigma]W[[j]]];
    If[verbose, 
     Print["\[Sigma]W[[i]] with basis=", basis, " of degree=", 
      polyDegree[\[Sigma]W[[j]], varSet], 
      ":\nF(a,s)=", -cMatrix // MatrixForm]];
    cMatrix = -cMatrix + \[Lambda]*IdentityMatrix[Length[cMatrix]];
    cMatrixSet2 = 
     Insert[cMatrixSet2, cMatrix, 
      Length[initIneq] + Length[unsafeIneq] + j];
    ];
   
   
   
   degree = Ceiling[polyDegreeMax[LieConstraints, varSet]/2];
   basis = monomList[varSet, degree];
   cMatrix = coefficientMatrix[varSet, basis, LieConstraints];
   If[verbose, 
    Print["LieConstraints with basis=", basis, " of degree=", 
     polyDegree[LieConstraints, varSet], 
     ":\nF(a,s)=", -cMatrix // MatrixForm]];
   cMatrix = -cMatrix + \[Lambda]*IdentityMatrix[Length[cMatrix]];
   AppendTo[cMatrixSet2, cMatrix];
   
   
   For[i = 1, i <= Length[cMatrixSet2], i++,
    If[i == 1, SDPVars = Variables[cMatrixSet2[[i]]], 
      SDPVars = 
       DeleteDuplicates[Join[SDPVars, Variables[cMatrixSet2[[i]]]]]];
    ];
   
   
   dcsigmaCoff = 
    Join[{\[Lambda]}, 
     Join @@ Table[
       Cases[SDPVars, 
        Subscript[ToExpression[StringJoin[ToString /@ {r, i}]], 
         Row[_]]], {i, 1, Length[initIneq]}], 
     Join @@ Table[
       Cases[SDPVars, 
        Subscript[ToExpression[StringJoin[ToString /@ {s, i}]], 
         Row[_]]], {i, 1, Length[initEq]}],
     Join @@ 
      Table[Cases[SDPVars, 
        Subscript[ToExpression[StringJoin[ToString /@ {t, i}]], 
         Row[_]]], {i, 1, Length[unsafeIneq]}], 
     Join @@ Table[
       Cases[SDPVars, 
        Subscript[ToExpression[StringJoin[ToString /@ {u, i}]], 
         Row[_]]], {i, 1, Length[unsafeEq]}], 
     Join @@ Table[
       Cases[SDPVars, 
        Subscript[ToExpression[StringJoin[ToString /@ {w, j}]], 
         Row[_]]], {j, 1, Length[domineq]}], 
     Join @@ Table[
       Cases[SDPVars, 
        Subscript[ToExpression[StringJoin[ToString /@ {y, j}]], 
         Row[_]]], {j, 1, Length[domeq]}]];
   
   positiveCoff = {};
   If[verbose, Print["dcsigmaCoff=", dcsigmaCoff]];
   bcCoff = Cases[SDPVars, Subscript[a, _]];
   dcpolyCoff = 
    Complement[SDPVars, bcCoff, dcsigmaCoff];
   If[verbose, Print["dcpolyCoff=", dcpolyCoff]];
   
   
   cSet = {0.5, 0.25, 0.75, 0, 1};
   cSet = {1};
   For[i = 1, i <= Length[cSet], i++,
    
    interDCinitial = 
     Thread[interCoff -> (cSet[[i]]*(interCoff1) + (1 - 
            cSet[[i]])*(interCoff2))];
    
    If[verbose, 
     Print["cSet[[i]]=", cSet[[i]], "   interDCTemp/.interDCinitial=",
       interDCTemp /. interDCinitial]];
    For[i = 1, i <= 5, i++,
     If[verbose, Print["inter-case: ", i]];
     
     If[DCADJudge == 0,
      DCround = 20;
      DCverbose = verbose;
      SeedRandom[i + seed];
      point = 
       DC[varSet, flowVec, rank, domineq, domeq, initIneq, 
        initEq, unsafeIneq, unsafeEq, paraRange, 
        LieOrder, \[Epsilon]interDC, \[Delta], bcTemp, cMatrixSet2, 
        positiveCoff, dcsigmaCoff, dcpolyCoff, DCround, DCverbose, 
        interDCinitial];
      bcCandidate = bcTemp /. point;
      If[verbose, 
       Print["interopolation-DC Condition: Barrier certificate candidate:", bcCandidate]];
      bcCoffMax = safeCoeffScale[bcCoff /. point];
      bcTempCoff = ((bcCoff /. point)/bcCoffMax) /. 
        x_ /; Abs[x] <= 10^-5 -> 0;
      bcTempCoff = bcTempCoff*bcCoffMax;
      bcCandidate = bcTemp /. (Thread[bcCoff -> bcTempCoff]);
      If[verbose, 
       Print["After estimating, bcCandidate=", bcCandidate]];
      
      {verifiedLie, verifiedUnsafe, verifiedInitial} = 
       Vertification[varSet, LieOrder, rank, flowVec, initIneq, 
        initEq, unsafeIneq, unsafeEq, bcCandidate, domineq, domeq, 
        point, verbose];
      If[verifiedLie && verifiedUnsafe && verifiedInitial, 
       If[verbose, 
        Print["interopolation-DC Condition-verification: True!"]]; 
       Break[], 
       If[verbose, 
        Print["interopolation-DC Condition-verification: False!"]]],
      
      ADround = 20;
      ADverbose = verbose;
      SeedRandom[i + seed];
      point = 
       AD[cMatrixSet2, bcCoff, positiveCoff, dcsigmaCoff, dcpolyCoff, 
        paraRange, \[Epsilon]interDC, ADround, ADverbose, 
        interDCinitial];
      
      bcCandidate = bcTemp /. point;
      If[verbose, 
       Print["interopolation-AD Condition: Barrier certificate candidate:", bcCandidate]];
      bcCoffMax = safeCoeffScale[bcCoff /. point];
      bcTempCoff = ((bcCoff /. point)/bcCoffMax) /. 
        x_ /; Abs[x] <= 10^-5 -> 0;
      bcTempCoff = bcTempCoff*bcCoffMax;
      bcCandidate = bcTemp /. (Thread[bcCoff -> bcTempCoff]);
      If[verbose, 
       Print["After estimating, bcCandidate=", bcCandidate]];
      
      {verifiedLie, verifiedUnsafe, verifiedInitial} = 
       Vertification[varSet, LieOrder, rank, flowVec, initIneq, 
        initEq, unsafeIneq, unsafeEq, bcCandidate, domineq, domeq, 
        point, verbose];
      If[verifiedLie && verifiedUnsafe && verifiedInitial, 
       If[verbose, 
        Print["interopolation-AD Condition-verification: True!"]]; 
       Break[], 
       If[verbose, 
        Print["interopolation-AD Condition-verification: False!"]]];
      ];
     ];
    ];
   
   
   InterDCTime = TimeUsed[] - InterDCTime;
   If[verbose, 
    Print["interopolation-time elapsed: ", InterDCTime, "s"]];
   Return[verifiedLie && verifiedUnsafe && verifiedInitial];
   ];

VectorBC[varSet_, flowVec_, bcTemp_, LieOrder_, rank_, initialineq_, 
   initialeq_, unsafeineq_, unsafeeq_, domineq_, domeq_, paraRange_, 
   polyAddDegree_, 
   LieSequence_, \[Epsilon]I_, \[Epsilon]U_, \[Epsilon]L_, 
   vectorNum_, \[Epsilon]Vector_, \[Delta]_, seed_, verbose_, 
   DCADJudge_] := 
  Module[{bcTempSet, LieSequenceSet, cMatrix, cMatrixSet, \[Sigma]I, \[Sigma]U, \[Sigma]W, polyTargetDegree, sosdegree, polydegree, sosSet, degree, basis, SDPVars, positiveCoff, sigmaCoff, polyCoff, bcCoff, DCround, DCverbose, point, bcCandidateSet, bcCoffMax, bcTempCoff, verifiedLie, verifiedUnsafe, verifiedInitial, ADround, ADverbose, number, initialComponents, unsafeComponents, initialIneqCompList, initialEqCompList, unsafeIneqCompList, unsafeEqCompList, comp, initialineqFlat, initialeqFlat, unsafeineqFlat, unsafeeqFlat},
    initialComponents = normalizeComponents[initialineq, initialeq];
    unsafeComponents = normalizeComponents[unsafeineq, unsafeeq];
    initialIneqCompList = 
     Table[DeleteCases[Flatten[initialComponents[[comp, 1]], Infinity], {}], {comp, 1, Length[initialComponents]}];
    initialEqCompList = 
     Table[DeleteCases[Flatten[initialComponents[[comp, 2]], Infinity], {}], {comp, 1, Length[initialComponents]}];
    unsafeIneqCompList = 
     Table[DeleteCases[Flatten[unsafeComponents[[comp, 1]], Infinity], {}], {comp, 1, Length[unsafeComponents]}];
    unsafeEqCompList = 
     Table[DeleteCases[Flatten[unsafeComponents[[comp, 2]], Infinity], {}], {comp, 1, Length[unsafeComponents]}];
   
   bcTempSet = 
    Table[polyTemp[varSet, identifier[{a, i}], 
      polyDegree[bcTemp, varSet]], {i, 1, vectorNum}];
   LieSequenceSet = 
    Table[LieDerivatives[varSet, flowVec, bcTempSet[[i]], 1], {i, 1, 
      vectorNum}];
   If[verbose, 
    Print["bcTempSet=", bcTempSet, " LieSequenceSet=", 
     LieSequenceSet]];
   
   
   sosSet = {};
   positiveCoff = {};
   \[Sigma]I = {};
   For[comp = 1, comp <= Length[initialIneqCompList], comp++,
    initialineqFlat = initialIneqCompList[[comp]];
    initialeqFlat = initialEqCompList[[comp]];
    If[Length[initialineqFlat] == 0 && Length[initialeqFlat] == 0, 
     Continue[]];
    polyTargetDegree = 
     degreeDecision[polyDegree[bcTemp, varSet], polyAddDegree, 
      initialineqFlat, initialeqFlat, varSet];
    If[Length[polyTargetDegree] == 0, 
     Print["I: component ", comp, " has wrong target degree."]; 
     Return[];];
    sosdegree = 
     Table[polyTargetDegree[[j]], {j, 1, Length[initialineqFlat]}];
    polydegree = 
     Table[polyTargetDegree[[Length[initialineqFlat] + j]], {j, 1, 
       Length[initialeqFlat]}];
    AppendTo[\[Sigma]I, 
     Table[Table[
       polyTemp[varSet, identifier[{r, comp, i, j}], sosdegree[[j]]], 
       {j, 1, Length[initialineqFlat]}], {i, 1, vectorNum}]];
    For[i = 1, i <= vectorNum, i++,
     AppendTo[
      sosSet, -bcTempSet[[i]] - 
       Sum[\[Sigma]I[[-1]][[i, j]]*initialineqFlat[[j]], {j, 1, 
         Length[initialineqFlat]}] + 
       Sum[polyTemp[varSet, identifier[{s, comp, i, j}], 
          polydegree[[j]]]*initialeqFlat[[j]], {j, 1, 
         Length[initialeqFlat]}] - \[Epsilon]I];
     ];
    For[j = 1, j <= Length[initialineqFlat], j++, 
     If[sosdegree[[j]] == 0, 
      positiveCoff = 
       Join[positiveCoff, 
        Table[\[Sigma]I[[-1]][[i, j]], {i, 1, vectorNum}]]]];
    If[verbose, 
     Print["initial#", comp, " sosdegree=", sosdegree, 
      "  initial polydegree=", polydegree, "  initial totaldegree=", 
      polyDegree[sosSet[[-1]], varSet]]];
    ];
   
   
   \[Sigma]U = {};
   For[comp = 1, comp <= Length[unsafeIneqCompList], comp++,
    unsafeineqFlat = unsafeIneqCompList[[comp]];
    unsafeeqFlat = unsafeEqCompList[[comp]];
    If[Length[unsafeineqFlat] == 0 && Length[unsafeeqFlat] == 0, 
     Continue[]];
    polyTargetDegree = 
     degreeDecision[polyDegree[bcTemp, varSet], polyAddDegree, 
      unsafeineqFlat, unsafeeqFlat, varSet];
    If[Length[polyTargetDegree] == 0, 
     Print["U: component ", comp, " has wrong target degree."]; 
     Return[];];
    sosdegree = 
     Table[polyTargetDegree[[i]], {i, 1, Length[unsafeineqFlat]}];
    polydegree = 
     Table[polyTargetDegree[[Length[unsafeineqFlat] + i]], {i, 1, 
       Length[unsafeeqFlat]}];
    AppendTo[\[Sigma]U, 
     Table[polyTemp[varSet, identifier[{t, comp, i}], sosdegree[[i]]], 
      {i, 1, Length[unsafeineqFlat]}]];
    AppendTo[sosSet, 
     Total[bcTempSet] - 
      Sum[\[Sigma]U[[-1]][[i]]*unsafeineqFlat[[i]], {i, 1, 
        Length[unsafeineqFlat]}] + 
      Sum[polyTemp[varSet, identifier[{u, comp, i}], polydegree[[i]]]*
        unsafeeqFlat[[i]], {i, 1, Length[unsafeeqFlat]}] - \[Epsilon]U];
    For[i = 1, i <= Length[unsafeineqFlat], i++, 
     If[sosdegree[[i]] == 0, 
      AppendTo[positiveCoff, \[Sigma]U[[-1]][[i]]]]];
    If[verbose, 
     Print["unsafe#", comp, " sosdegree=", sosdegree, 
      "  unsafe polydegree=", polydegree, "  unsafe totaldegree=", 
      polyDegree[sosSet[[-1]], varSet]]];
    ];
   
   
   
   \[Sigma]W = {};
   polyTargetDegree = 
    degreeDecision[polyDegree[LieSequence[[2]], varSet], 0, domineq, 
     domeq, varSet];
   
   sosdegree = Table[polyTargetDegree[[j]], {j, 1, Length[domineq]}];
   
   polydegree = 
    Table[polyTargetDegree[[Length[domineq] + j]], {j, 1, 
      Length[domeq]}];
   For[i = 1, i <= vectorNum, i++,
    AppendTo[\[Sigma]W, 
     Table[polyTemp[varSet, identifier[{w, i, j}], 
       sosdegree[[j]]], {j, 1, Length[domineq]}]];
    
    AppendTo[
     sosSet, -LieSequenceSet[[i]][[2]] + 
      Sum[identifier[{c, i, j}]*bcTempSet[[j]], {j, 1, vectorNum}] - 
      Sum[\[Sigma]W[[i]][[j]]*domineq[[j]], {j, 1, Length[domineq]}] +
       Sum[polyTemp[varSet, identifier[{y, i, j}], polydegree[[j]]]*
        domeq[[j]], {j, 1, Length[domeq]}] - \[Epsilon]L];
    ];
   
   For[j = 1, j <= Length[domineq], j++, If[sosdegree[[j]] == 0,
     positiveCoff = 
      Join[positiveCoff, 
       Table[polyTemp[varSet, identifier[{w, i, j}], 
         sosdegree[[j]]], {i, 1, vectorNum}]]]];
   If[verbose, 
    Print["Lie sosdegree=", sosdegree, "  Lie polydegree=", 
     polydegree, "  Lie totaldegree=", 
     polyDegree[sosSet[[-1]], varSet]]];
   sosSet = 
    Map[Collect[#, varSet, Simplify] &, 
     Join[Flatten[\[Sigma]I, Infinity], Flatten[\[Sigma]U, Infinity], 
      Flatten[\[Sigma]W, Infinity], 
      sosSet]];
   If[verbose, Print["SOS constraints:\n", sosSet]];
   
   
   
   cMatrixSet = {};
   For[j = 1, j <= Length[sosSet], j++,
    degree = Ceiling[polyDegreeMax[sosSet[[j]], varSet]/2];
    basis = monomList[varSet, degree];
    cMatrix = coefficientMatrix[varSet, basis, sosSet[[j]]];
    If[verbose, 
     Print["sosSet[[i]] with basis=", basis, " of degree=", 
      polyDegree[sosSet[[j]], varSet], 
      ":\nF(a,s)=", -cMatrix // MatrixForm]];
    cMatrix = -cMatrix + \[Lambda]*IdentityMatrix[Length[cMatrix]];
    AppendTo[cMatrixSet, cMatrix];
    ];
   cMatrix = 
    DiagonalMatrix[
     Join[Join @@ 
       Table[identifier[{c, i, j}], {i, 1, vectorNum}, {j, 1, i - 1}],
       Join @@ 
       Table[identifier[{c, i, j}], {i, 1, vectorNum}, {j, i + 1, 
         vectorNum}]]];
   AppendTo[
    cMatrixSet, -cMatrix + \[Lambda]*
      IdentityMatrix[Length[cMatrix]]];
   If[verbose, Print["cMatrixSet=", cMatrixSet // MatrixForm]];
   
   For[i = 1, i <= Length[cMatrixSet], i++,
    If[i == 1, SDPVars = Variables[cMatrixSet[[i]]], 
      SDPVars = 
       DeleteDuplicates[Join[SDPVars, Variables[cMatrixSet[[i]]]]]];
    ];
   If[verbose, Print["SDPVars=", SDPVars]];
  positiveCoff = 
   Join[positiveCoff, 
    Join @@ Table[
      identifier[{c, i, j}], {i, 1, vectorNum}, {j, 1, i - 1}], 
    Join @@ Table[
      identifier[{c, i, j}], {i, 1, vectorNum}, {j, i + 1, 
       vectorNum}]];
  If[! TrueQ[$EnableVectorPositiveCoff], positiveCoff = {}];
  positiveCoff = DeleteDuplicates[Flatten[positiveCoff]];
   sigmaCoff = 
    Join[{\[Lambda]}, 
     Flatten@Table[
       Cases[SDPVars, 
        Subscript[
         ToExpression[StringJoin[ToString /@ {r, comp, i, j}]], 
         Row[_]]], {comp, 1, Length[initialIneqCompList]}, {i, 1, 
        vectorNum}, {j, 1, Length[initialIneqCompList[[comp]]]}], 
     Flatten@Table[
       Cases[SDPVars, 
        Subscript[
         ToExpression[StringJoin[ToString /@ {s, comp, i, j}]], 
         Row[_]]], {comp, 1, Length[initialEqCompList]}, {i, 1, 
        vectorNum}, {j, 1, Length[initialEqCompList[[comp]]]}], 
     Flatten@Table[
       Cases[SDPVars, 
        Subscript[
         ToExpression[StringJoin[ToString /@ {t, comp, i}]], 
         Row[_]]], {comp, 1, Length[unsafeIneqCompList]}, {i, 1, 
        Length[unsafeIneqCompList[[comp]]]}], 
     Flatten@Table[
       Cases[SDPVars, 
        Subscript[
         ToExpression[StringJoin[ToString /@ {u, comp, i}]], 
         Row[_]]], {comp, 1, Length[unsafeEqCompList]}, {i, 1, 
        Length[unsafeEqCompList[[comp]]]}], 
     Flatten@Table[
       Cases[SDPVars, 
        Subscript[ToExpression[StringJoin[ToString /@ {w, i, j}]], 
         Row[_]]], {i, 1, vectorNum}, {j, 1, Length[domineq]}], 
     Flatten@Table[
       Cases[SDPVars, 
        Subscript[ToExpression[StringJoin[ToString /@ {y, i, j}]], 
         Row[_]]], {i, 1, vectorNum}, {j, 1, Length[domeq]}]];
   
   If[verbose, Print["positiveCoff=", positiveCoff]];
   If[verbose, Print["sigmaCoff=", sigmaCoff]];
   bcCoff = 
    Join @@ Table[
      Cases[SDPVars, 
       Subscript[ToExpression[StringJoin[ToString /@ {a, i}]], 
        Row[_]]], {i, 1, vectorNum}];
   SDPVars = DeleteDuplicates[Flatten[SDPVars]];
   sigmaCoff = DeleteDuplicates[Flatten[sigmaCoff]];
   bcCoff = DeleteDuplicates[Flatten[bcCoff]];
   polyCoff = Complement[SDPVars, bcCoff, sigmaCoff];
   If[verbose, Print["polyCoff=", polyCoff]];
   number = 0;
   verificationverbose = False;
   While[number < 10, number++;
    If[verbose, Print["Cases & SeedRandom: ", number]];
    If[DCADJudge == 0,
     
     SeedRandom[number + seed];
     
     DCround = 20;
     DCverbose = False;
     point = 
      TimeConstrained[
       DC[varSet, flowVec, rank, domineq, domeq, initialineq, 
        initialeq, unsafeineq, unsafeeq, paraRange, 
        LieOrder, \[Epsilon]Vector, \[Delta], bcTempSet, cMatrixSet, 
        positiveCoff, sigmaCoff, polyCoff, DCround, DCverbose, 
        Automatic], $MethodCallTimeLimit, $Failed];
     If[point === $Failed, 
      If[verbose && TrueQ[$SDPWarnOnFailure], 
       logWarn["vectorBC DC step timed out. Trying next seed."]]; 
      Continue[]];
     bcCandidateSet = bcTempSet /. point;
     If[verbose, 
      Print["vectorBC-DC Condition: Barrier certificate candidate set:", bcCandidateSet]];
     bcCoffMax = safeCoeffScale[bcCoff /. point];
     bcTempCoff = ((bcCoff /. point)/bcCoffMax) /. 
       x_ /; Abs[x] <= 10^-5 -> 0;
     bcTempCoff = bcTempCoff*bcCoffMax;
     bcCandidateSet = bcTempSet /. (Thread[bcCoff -> bcTempCoff]);
     If[verbose, 
      Print["After estimating, bcCandidate=", bcCandidateSet]];
     
     {verifiedLie, verifiedUnsafe, verifiedInitial} = 
      Vertification[varSet, LieOrder, rank, flowVec, initialineq, 
       initialeq, unsafeineq, unsafeeq, bcCandidateSet, domineq, 
       domeq, point, verificationverbose];
     If[verifiedLie && verifiedUnsafe && verifiedInitial, 
      Print["vectorBC-DC Condition-verification: True!"]; Break[], 
      If[verbose, 
       Print["vectorBC-DC Condition-verification: False!"]]],
     
     SeedRandom[number + seed];
     ADround = 20;
     ADverbose = False;
     point = 
      TimeConstrained[
       AD[cMatrixSet, bcCoff, positiveCoff, sigmaCoff, polyCoff, 
        paraRange, \[Epsilon]Vector, ADround, ADverbose, Automatic], 
       $MethodCallTimeLimit, $Failed];
     If[point === $Failed, 
      If[verbose && TrueQ[$SDPWarnOnFailure], 
       logWarn["vectorBC AD step timed out. Trying next seed."]]; 
      Continue[]];
     bcCandidateSet = bcTempSet /. point;
     If[verbose, 
      Print["vectorBC-AD Condition: Barrier certificate candidate set:", bcCandidateSet]];
     
     
     {verifiedLie, verifiedUnsafe, verifiedInitial} = 
      Vertification[varSet, LieOrder, rank, flowVec, initialineq, 
       initialeq, unsafeineq, unsafeeq, bcCandidateSet, domineq, 
       domeq, point, verificationverbose];
     If[verifiedLie && verifiedUnsafe && verifiedInitial, 
      If[verbose, Print["vectorBC-AD Condition-verification: True!"]];
       Break[], 
      If[verbose, 
       Print["vectorBC-AD Condition-verification: False!"]]];
     ];
    ];
   
   Return[verifiedLie && verifiedUnsafe && verifiedInitial];
   ];

   processProblemRaw[problemRaw_, verbose_, \[Epsilon]_] := 
  Module[{ineqsRaw, ineqsMark, A, Ineqs, StrictIneqs, eqsRaw, Eqs},
   
   
   ineqsRaw = {{}, {}, {}, {}};
   ineqsMark = {};
   For[i = 1, i <= Length[problemRaw], i++,
    A = Join @@ 
      StringCases[problemRaw[[i]], 
       RegularExpression[
         "(.*)\\s*<=\\s*(.*)\\s*"] :> {ToExpression[
          StringReplace["$1", 
           RegularExpression["([a-zA-Z]+)(\\d+)"] -> 
            "Subscript[$1,$2]"]], 
         ToExpression[
          StringReplace["$2", 
           RegularExpression["([a-zA-Z]+)(\\d+)"] -> 
            "Subscript[$1,$2]"]]}];
    If[Length[A] > 0, AppendTo[ineqsRaw[[1]], A]; 
     AppendTo[ineqsMark, i]; Continue[]];
    A = Join @@ 
      StringCases[problemRaw[[i]], 
       RegularExpression[
         "(.*)\\s*>=\\s*(.*)\\s*"] :> {ToExpression[
          StringReplace["$1", 
           RegularExpression["([a-zA-Z]+)(\\d+)"] -> 
            "Subscript[$1,$2]"]], 
         ToExpression[
          StringReplace["$2", 
           RegularExpression["([a-zA-Z]+)(\\d+)"] -> 
            "Subscript[$1,$2]"]]}];
    If[Length[A] > 0, AppendTo[ineqsRaw[[2]], A]; 
     AppendTo[ineqsMark, i]; Continue[]];
    A = Join @@ 
      StringCases[problemRaw[[i]], 
       RegularExpression[
         "(.*)\\s*>\\s*(.*)\\s*"] :> {ToExpression[
          StringReplace["$1", 
           RegularExpression["([a-zA-Z]+)(\\d+)"] -> 
            "Subscript[$1,$2]"]], 
         ToExpression[
          StringReplace["$2", 
           RegularExpression["([a-zA-Z]+)(\\d+)"] -> 
            "Subscript[$1,$2]"]]}];
    If[Length[A] > 0, AppendTo[ineqsRaw[[3]], A]; 
     AppendTo[ineqsMark, i]; Continue[]];
    A = Join @@ 
      StringCases[problemRaw[[i]], 
       RegularExpression[
         "(.*)\\s*<\\s*(.*)\\s*"] :> {ToExpression[
          StringReplace["$1", 
           RegularExpression["([a-zA-Z]+)(\\d+)"] -> 
            "Subscript[$1,$2]"]], 
         ToExpression[
          StringReplace["$2", 
           RegularExpression["([a-zA-Z]+)(\\d+)"] -> 
            "Subscript[$1,$2]"]]}];
    If[Length[A] > 0, AppendTo[ineqsRaw[[4]], A]; 
     AppendTo[ineqsMark, i]; Continue[]];
    ];
   If[verbose, Print["ineqsRaw=", ineqsRaw]];
   Ineqs = {};
   If[Length[ineqsRaw[[1]]] > 0 || Length[ineqsRaw[[2]]] > 0,
    If[Length[ineqsRaw[[1]]] > 0, 
     Ineqs = Join[Ineqs, #2 - #1 & @@@ ineqsRaw[[1]]]];
    If[Length[ineqsRaw[[2]]] > 0, 
     Ineqs = Join[Ineqs, #1 - #2 & @@@ ineqsRaw[[2]]]]];
   If[verbose, Print["Ineqs=", Ineqs]];
   StrictIneqs = {};
   If[Length[ineqsRaw[[3]]] > 0 || Length[ineqsRaw[[4]]] > 0,
    If[Length[ineqsRaw[[3]]] > 0, 
     StrictIneqs = 
      Join[StrictIneqs, #1 - #2 - \[Epsilon] & @@@ ineqsRaw[[3]]]];
    If[Length[ineqsRaw[[4]]] > 0, 
     StrictIneqs = 
      Join[StrictIneqs, #2 - #1 - \[Epsilon] & @@@ ineqsRaw[[4]]]]];
   If[verbose, Print["StrictIneqs=", StrictIneqs]];
   
   
   eqsRaw = {};
   For[i = 1, i <= Length[problemRaw], i++,
    If[MemberQ[ineqsMark, i], Null, 
     AppendTo[eqsRaw, 
      Join @@ StringCases[problemRaw[[i]], 
        RegularExpression[
          "(.*)\\s*=\\s*(.*)\\s*"] :> {ToExpression[
           StringReplace["$1", 
            RegularExpression["([a-zA-Z]+)(\\d+)"] -> 
             "Subscript[$1,$2]"]], 
          ToExpression[
           StringReplace["$2", 
            RegularExpression["([a-zA-Z]+)(\\d+)"] -> 
             "Subscript[$1,$2]"]]}]];
     ];
    ];
   If[verbose, Print["eqsRaw=", eqsRaw]];
   Eqs = If[Length[eqsRaw] > 0, #2 - #1 & @@@ eqsRaw, {}];
   If[verbose, Print["Eqs=", Eqs]];
   Return[{Ineqs, StrictIneqs, Eqs}];
   ];


parseBenchmark[input_String, verbose_] := 
  Module[{vars, flowEq, problemRawTemp, problemRaw, initialIneqs, initialStrictIneqs, initialEqs, unsafeIneqs, unsafeStrictIneqs, unsafeEqs, ansIneqs, ansStrictIneqs, ansEqs, \[Epsilon], initialineqs, initialeqs, unsafeineqs, unsafeeqs, domainineqs, domaineqs, ansineqs, initial, unsafe, barrierDegree, polyAddDegree, paraRange, LieOrder, \[Epsilon]I, \[Epsilon]U, \[Epsilon]L, \[Epsilon]DC, \[Epsilon]AD, \[Epsilon]Vector, \[Delta], seed, verbose1, domainIneqs, domainStrictIneqs, domainEqs, implicitVar, implicitRule, implicitEqVars, tempans, ans, timesum, initialEqForImplicit, unresolvedImplicitVar, fixedImplicitVar, solveRes, vals, initialeqsRun, unsafeeqsRun, domaineqsRun, k},
   \[Epsilon] = N[10^-7];
   
   vars = 
    StringCases[input, 
     RegularExpression[
       "Real\\s+([a-zA-Z][a-zA-Z0-9_]*(?:,\\s*[a-zA-Z][a-zA-Z0-9_]*)*)"] :> "$1"];
   vars = Flatten[StringSplit[#, ","] & /@ vars];
   vars = StringTrim /@ vars;
   vars = 
    ToExpression[
     StringReplace[vars, 
      RegularExpression["([a-zA-Z]+)(\\d+)"] -> "Subscript[$1,$2]"]];
   If[verbose, Print["vars=", vars]];
   
   
   flowEq = 
    StringCases[input, 
     RegularExpression[
       "(\\w+)'(\\s*)=(\\s*)(.*?)(\\s*)(?:,|\\}|\\&|\\@|\\])"] :> {"$1", 
       "$4"}];
   vars = 
    ToExpression[
     StringReplace[Table[flowEq[[i]][[1]], {i, 1, Length[flowEq]}], 
      RegularExpression["([a-zA-Z]+)(\\d+)"] -> "Subscript[$1,$2]"]];
   flowEq = 
    ToExpression[
     StringReplace[Table[flowEq[[i]][[2]], {i, 1, Length[flowEq]}], 
      RegularExpression["([a-zA-Z]+)(\\d+)"] -> "Subscript[$1,$2]"]];
   If[verbose, Print["vars=", vars]];
   If[verbose, Print["flowEq=", flowEq]];
   
   
   
   problemRaw = 
    StringReplace[
     StringCases[input, 
      RegularExpression["Problem\\s*([\\s\\S]*?)\\s*->"] :> 
       "$1"], {" " -> "", "\n" -> ""}];
   If[verbose, Print["problemRaw=", problemRaw]];
   If[StringContainsQ[problemRaw, "|"] == {True},
    problemRaw = Join @@ StringSplit[problemRaw, "|"];
    If[verbose, Print["problemRaw=", problemRaw]];
    initialIneqs = initialStrictIneqs = initialEqs = {};
    For[k = 1, k <= Length[problemRaw], k++,
     problemRawTemp = 
      StringCases[problemRaw[[k]], 
       RegularExpression["(\\()(.*)(\\))"] -> "$2"];
     If[verbose, Print["problemRawTemp=", problemRawTemp]];
     problemRawTemp = 
      Join @@ StringCases[problemRawTemp, 
        RegularExpression[
          "[\\w\\^\\*\\+\\-\\./\\(\\)\\s]+[<>=]+[\\w\\^\\*\\+\\-\\./\\(\\)\\s]+"] -> "$0"];
     If[verbose, Print["problemRawTemp=", problemRawTemp]];
     If[verbose, Print["Processing initial problemRawTemp:"]];
     initial = 
      processProblemRaw[problemRawTemp, verbose, \[Epsilon]];
     AppendTo[initialIneqs, initial[[1]]];
     AppendTo[initialStrictIneqs, initial[[2]]];
     AppendTo[initialEqs, initial[[3]]];
     ],
    problemRaw = 
     Join @@ StringCases[problemRaw, 
       RegularExpression[
         "[\\w\\^\\*\\+\\-\\./\\(\\)\\s]+[<>=]+[\\w\\^\\*\\+\\-\\./\\(\\)\\s]+"] -> "$0"];
    If[verbose, Print["problemRaw=", problemRaw]];
    If[verbose, Print["Processing initial problemRaw:"]];
    {initialIneqs, initialStrictIneqs, initialEqs} = 
     processProblemRaw[
      If[ListQ[problemRaw], problemRaw, {problemRaw}], verbose, 
      \[Epsilon]];
    ];
   If[verbose, 
    Print["{initialIneqs,initialStrictIneqs,initialEqs}=", {initialIneqs, initialStrictIneqs, initialEqs}]];
   
   
   problemRaw = 
    StringReplace[
     StringCases[input, 
      RegularExpression["\\]\\s*\\!\\s*\\(?\\s*([\\s\\S]*?)\\s*\\)?\\s*End\\.?"] :> 
       "$1"], {" " -> "", "\n" -> ""}];
   If[verbose, Print["problemRaw=", problemRaw]];
   If[StringContainsQ[problemRaw, "|"] == {True},
    problemRaw = Join @@ StringSplit[problemRaw, "|"];
    If[verbose, Print["problemRaw=", problemRaw]];
    unsafeIneqs = unsafeStrictIneqs = unsafeEqs = {};
    For[k = 1, k <= Length[problemRaw], k++,
     problemRawTemp = 
      StringCases[problemRaw[[k]], 
       RegularExpression["(\\()(.*)(\\))"] -> "$2"];
     If[verbose, Print["problemRawTemp=", problemRawTemp]];
     problemRawTemp = 
      Join @@ StringCases[problemRawTemp, 
        RegularExpression[
          "[\\w\\^\\*\\+\\-\\./\\(\\)\\s]+[<>=]+[\\w\\^\\*\\+\\-\\./\\(\\)\\s]+"] -> "$0"];
     If[verbose, Print["problemRawTemp=", problemRawTemp]];
     If[verbose, Print["Processing unsafe problemRawTemp:"]];
     unsafe = processProblemRaw[problemRawTemp, verbose, \[Epsilon]];
     AppendTo[unsafeIneqs, unsafe[[1]]];
     AppendTo[unsafeStrictIneqs, unsafe[[2]]];
     AppendTo[unsafeEqs, unsafe[[3]]];
     ],
    problemRaw = 
     Join @@ StringCases[problemRaw, 
       RegularExpression[
         "[\\w\\^\\*\\+\\-\\./\\(\\)\\s]+[<>=]+[\\w\\^\\*\\+\\-\\./\\(\\)\\s]+"] -> "$0"];
    If[verbose, Print["problemRaw=", problemRaw]];
    If[verbose, Print["Processing unsafe problemRaw:"]];
    {unsafeIneqs, unsafeStrictIneqs, unsafeEqs} = 
     processProblemRaw[
      If[ListQ[problemRaw], problemRaw, {problemRaw}], verbose, 
      \[Epsilon]];
    ];
   If[verbose, 
    Print["{unsafeIneqs,unsafeStrictIneqs,unsafeEqs}=", {unsafeIneqs, 
      unsafeStrictIneqs, unsafeEqs}]];
   
   
   
   {domainIneqs, domainStrictIneqs, domainEqs} = {{}, {}, {}};
   problemRaw = 
    StringCases[input, 
     RegularExpression["\\[([\\s\\S]*?)\\]"] -> "$1"];
   If[verbose, Print["problemRaw=", problemRaw]];
   problemRaw = 
    Join @@ StringCases[problemRaw, 
      RegularExpression["\\&([\\s\\S]*?)\\@"] -> "$1"];
   If[problemRaw === {} || problemRaw === "",
    problemRaw = 
     Join @@ StringCases[
       StringCases[input, 
        RegularExpression["\\[([\\s\\S]*?)\\]"] -> "$1"], 
       RegularExpression["\\&([\\s\\S]*)"] -> "$1"];
    ];
   problemRaw = 
    StringReplace[problemRaw, {" " -> "", "\n" -> ""}];
   If[verbose, Print["problemRaw=", problemRaw]];
   If[Length[problemRaw] != 0,
    problemRaw = 
     Join @@ StringCases[problemRaw, 
       RegularExpression[
         "[\\w\\^\\*\\+\\-\\./\\(\\)\\s]+[<>=]+[\\w\\^\\*\\+\\-\\./\\(\\)\\s]+"] -> "$0"];
    If[verbose, Print["problemRaw=", problemRaw]];
    If[verbose, Print["Processing domain problemRaw:"]];
    {domainIneqs, domainStrictIneqs, domainEqs} = 
     processProblemRaw[
      If[ListQ[problemRaw], problemRaw, {problemRaw}], verbose, 
      \[Epsilon]];
    If[verbose, 
     Print["{domainIneqs,domainStrictIneqs,domainEqs}=", {domainIneqs,
        domainStrictIneqs, domainEqs}]];
    ];
   
   isListOfListsQ[z_] := ListQ[z] && z =!= {} && AllTrue[z, ListQ];
   If[isListOfListsQ[initialIneqs], 
    initialineqs = 
     Table[Join[initialIneqs[[i]], initialStrictIneqs[[i]]], {i, 1, 
       Length[initialIneqs]}];
    initialeqs = initialEqs,
    initialineqs = {Join[initialIneqs, initialStrictIneqs]}; 
    initialeqs = {initialEqs}];
   If[isListOfListsQ[unsafeIneqs], 
    unsafeineqs = 
     Table[Join[unsafeIneqs[[i]], unsafeStrictIneqs[[i]]], {i, 1, 
       Length[unsafeIneqs]}];
    unsafeeqs = unsafeEqs,
   unsafeineqs = {Join[unsafeIneqs, unsafeStrictIneqs]}; 
   unsafeeqs = {unsafeEqs}];
   If[ListQ[initialineqs] && Length[initialineqs] == 1 && 
     ListQ[initialineqs[[1]]], initialineqs = initialineqs[[1]]];
   If[ListQ[initialeqs] && Length[initialeqs] == 1 && 
     ListQ[initialeqs[[1]]], initialeqs = initialeqs[[1]]];
   If[ListQ[unsafeineqs] && Length[unsafeineqs] == 1 && 
     ListQ[unsafeineqs[[1]]], unsafeineqs = unsafeineqs[[1]]];
   If[ListQ[unsafeeqs] && Length[unsafeeqs] == 1 && 
     ListQ[unsafeeqs[[1]]], unsafeeqs = unsafeeqs[[1]]];
   domainineqs = Join[domainIneqs, domainStrictIneqs];
   domaineqs = domainEqs;
   problemRaw = 
    StringReplace[
     StringCases[input, 
      RegularExpression["invariant\\(\\s*([\\s\\S]*?)\\)\\s\\]"] :> 
       "$1"], {" " -> "", "\n" -> ""}];
   If[verbose, Print["pegasus Raw ans=", problemRaw]];
   problemRaw = 
    Join @@ StringCases[problemRaw, 
      RegularExpression[
        "[\\w\\^\\*\\+\\-\\./\\(\\)\\s]+[<>=]+[\\w\\^\\*\\+\\-\\./\\(\\)\\s]+"] -> "$0"];
   If[verbose, Print["pegasus Raw ans=", problemRaw]];
   If[verbose, Print["Processing pegasus Raw ans:"]];
   {ansIneqs, ansStrictIneqs, ansEqs} = 
    -processProblemRaw[
      If[ListQ[problemRaw], problemRaw, {problemRaw}], verbose, 
      \[Epsilon]];
   
   If[verbose, Print["{ansIneqs,ansStrictIneqs,ansEqs}=", {ansIneqs, ansStrictIneqs, ansEqs}]];
   ansineqs = Join[ansIneqs, ansStrictIneqs];
   If[verbose, 
    logDebug["vars=" <> ToString[vars, InputForm] <> 
      " flowEq=" <> ToString[flowEq, InputForm]];
    logDebug["initialineqs=" <> ToString[initialineqs, InputForm]];
    logDebug["initialeqs=" <> ToString[initialeqs, InputForm]];
    logDebug["unsafeineqs=" <> ToString[unsafeineqs, InputForm]];
    logDebug["unsafeeqs=" <> ToString[unsafeeqs, InputForm]];
    logDebug["domainineqs=" <> ToString[domainineqs, InputForm]];
    logDebug["domaineqs=" <> ToString[domaineqs, InputForm]];
    logDebug["ansineqs=" <> ToString[ansineqs, InputForm]];
    ];
   
   
   
   seed = 0;
   time = TimeUsed[];
   ans = {};
   timesum = TimeUsed[];
   polyAddDegree = 3; 
   paraRange = {-1, 1}; 
   LieOrder = 1; 
   \[Epsilon]I = 0; \[Epsilon]U = \[Epsilon]L = N[10^-7]; \[Epsilon]Vector = \[Epsilon]DC = \[Epsilon]AD = N[10^-5]; \[Delta] = -N[10^-6]; 
   verbose1 = False;
   implicitRule = {};
   implicitVar = Complement[Variables[Join[Flatten[initialineqs, 1], Flatten[initialeqs, 1], Flatten[unsafeineqs, 1], Flatten[unsafeeqs, 1], domainineqs, domaineqs, flowEq]], vars];
   If[verbose, logDebug["implicitVar=" <> ToString[implicitVar, InputForm]]];
   If[Length[implicitVar] > 0,
    initialEqForImplicit = DeleteCases[Flatten[{initialeqs}, Infinity], 0];
    implicitEqVars = Intersection[implicitVar, Variables[initialEqForImplicit]];
    implicitRule = {};
    If[Length[implicitEqVars] > 0 && Length[initialEqForImplicit] > 0,
     solveRes = 
      Quiet[Solve[
        Thread[initialEqForImplicit == 0], implicitEqVars, Reals]];
     If[ListQ[solveRes] && solveRes =!= {},
      implicitRule = 
       DeleteDuplicates[
        Flatten[
         Table[vals = 
            DeleteDuplicates[
             Cases[solveRes, Rule[implicitEqVars[[k]], rhs_] :> rhs, 
              Infinity]];
           vals = Select[vals, Variables[#] === {} &];
           If[Length[vals] == 1, implicitEqVars[[k]] -> vals[[1]], 
            Sequence @@ {}], {k, 1, Length[implicitEqVars]}]]]
      ]
     ];
    If[verbose, logDebug["implicitRule=" <> ToString[implicitRule, InputForm]]];
    fixedImplicitVar = 
     DeleteDuplicates[First /@ Select[implicitRule, MatchQ[#, _Rule] &]];
    unresolvedImplicitVar = Complement[implicitVar, fixedImplicitVar];
    If[Length[unresolvedImplicitVar] > 0,
     logWarn[
      "Unsupported parameter case: unresolved parameters " <> 
       ToString[unresolvedImplicitVar, InputForm]];
     Return[{"UnsupportedParameterCase", unresolvedImplicitVar}]
     ];
    ];
   initialeqsRun = dropTrivialZeroConstraints[initialeqs /. implicitRule];
   unsafeeqsRun = dropTrivialZeroConstraints[unsafeeqs /. implicitRule];
   domaineqsRun = dropTrivialZeroConstraints[domaineqs /. implicitRule];
   logInfo[
    "Problem parsed: vars=" <> ToString[vars, InputForm] <> 
     ", implicit rules=" <> ToString[implicitRule, InputForm] <> "."];
   If[Length[vars] == 2, barrierDegree = 6, barrierDegree = 3];
   If[verbose,
    logDebug["flowEq=" <> ToString[flowEq /. implicitRule, InputForm]];
    logDebug["initial=" <> 
      ToString[{initialineqs /. implicitRule, initialeqsRun}, InputForm]];
    logDebug["unsafe=" <> 
      ToString[{unsafeineqs /. implicitRule, unsafeeqsRun}, InputForm]];
    logDebug["domain=" <> 
      ToString[{domainineqs /. implicitRule, domaineqsRun}, InputForm]];
    ];
   tempans = 
    main[vars, flowEq /. implicitRule, domainineqs /. implicitRule, 
     domaineqsRun, initialineqs /. implicitRule, initialeqsRun, 
     unsafeineqs /. implicitRule, unsafeeqsRun, barrierDegree, 
     polyAddDegree, paraRange, LieOrder, \[Epsilon]I, \[Epsilon]U, 
     \[Epsilon]L, \[Epsilon]DC, \[Epsilon]AD, \[Epsilon]Vector, \[Delta],
      seed, verbose1, Automatic];
   ans = Join[ans, tempans];
   If[ListQ[tempans] && Length[tempans] >= 1 && NumericQ[tempans[[1]]] && 
      TrueQ[tempans[[1]] > 0] && (TimeUsed[] - timesum) <= 3600, 
    Return[ans], 
    logWarn["Solver failed or returned unknown result: " <> 
      ToString[tempans, InputForm]]];
   Return[{-1, 0, 0}];
];


processFile[filePath_String, caseNumbers_List] := 
  Module[{rawRTFText, rawText, caseBlocks, verbose, inputString, caseId, result, successCount, failCount},
   rawRTFText = Import[filePath, "Text"];
   rawText = 
    StringReplace[rawRTFText, RegularExpression["\\\\[a-zA-Z]+[0-9]*|\\{\\}|\\{|\\}"] -> ""];
   rawText = StringReplace[rawText, RegularExpression["\\\\"] -> ""];
   caseBlocks = 
    StringCases[rawText, 
     RegularExpression["(?s)ProgramVariables.*?End\\.\\s*Problem.*?End\\."] -> {"$0"}];
   verbose = False;
   successCount = 0;
   failCount = 0;
   Do[
    If[caseId < 1 || caseId > Length[caseBlocks],
     logError["Case " <> ToString[caseId] <> " is out of range."];
     failCount++;
     Continue[]
     ];
    $CurrentCaseId = caseId;
    $CaseId = caseId;
    $CaseImageIndex = 0;
    inputString = ToString[caseBlocks[[caseId]]];
    logInfo["Benchmark definition:\n" <> inputString];
    result = parseBenchmark[inputString, verbose];
    logInfo["Case result: " <> ToString[result, InputForm]];
    If[ListQ[result] && Length[result] >= 1 && NumericQ[result[[1]]] && 
      result[[1]] > 0, successCount++, failCount++];
    , {caseId, caseNumbers}];
   logInfo[
    "Run summary: success=" <> ToString[successCount] <> ", fail=" <> 
     ToString[failCount] <> "."];
   ];
   
filePath = ".../Mar2.0/Differential-invariant-generator/Pegasus_benchmark.rtf";
caseNumbers = {41}; 
processFile[filePath, caseNumbers];
