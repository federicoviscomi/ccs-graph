(* ::Package:: *)

BeginPackage["CcsTool`"]


getCcsGraph::usage="getCcsGraph[process, definitions, iterationLimit] prende in input: un processo CCS, una sequenza di definizioni di identificatori separate da punto e virgola, un intero che limita il numero di iterazioni dell'algoritmo. Restituisce in output la semantica del processo di input"


Begin["`Private`"]



ToSyntNode[start_,end_]:=
Which[
	Length[start]==0,
	{start,end},

	Length[start]>0,
	Which[
		MatchQ[start[[1]],"+"],
		ToSyntNode[Rest[start],Append[end,CcsSum["_","_"]]],

		MatchQ[start[[1]],"|"],
		ToSyntNode[Rest[start],Append[end,CcsPar["_","_"]]],

		MatchQ[StringTake[start[[1]],-1],"."],
		If[MatchQ[StringTake[start[[1]],1],":"],
			ToSyntNode[Rest[start],Append[end,CcsCat[CcsCom[CcsAct[StringDrop[StringDrop[start[[1]],-1],1]]],"_"]]],
			ToSyntNode[Rest[start],Append[end,CcsCat[CcsAct[StringDrop[start[[1]],-1]],"_"]]]
		],

		MatchQ[StringTake[start[[1]],-1],"/"],
		ToSyntNode[
			Rest[start],
			Append[end,CcsRes[Select[Flatten[(StringSplit[#1,x:"{"|"}":>x]&)/@StringTrim/@StringSplit[StringDrop[start[[1]],-1]]],!MatchQ[#1,"{"]&&!MatchQ[#1,"}"]&],"_"]]
		],

		MatchQ[start[[1]],"("]||MatchQ[start[[1]],")"]||MatchQ[start[[1]],"0"]||MatchQ[start[[1]],"$"],
		ToSyntNode[Rest[start],Append[end,start[[1]]]],

		True,
		ToSyntNode[Rest[start],Append[end,CcsIde[start[[1]]]]]
	]
]


mergeActionWithDot[start_,end_]:=
Which[
	Length[start]==0,
	end,

	Length[start]==1,
	Append[end,start[[1]]],

	Length[start]>1,
	If[MatchQ[start[[2]],"."],
		mergeActionWithDot[Drop[start,2],Append[end,StringJoin[start[[1]],"."]]],
		mergeActionWithDot[Rest[start], Append[end,start[[1]]]]
	]
]


mergeRestriction[start_, end_]:=
Which[
	Length[start]==0,
	end,	

	Length[start]>0,
	If[MatchQ[start[[1]],"{"],
		mergeRestriction[Drop[start,4], Append[end,StringJoin[start[[1]],start[[2]],start[[3]],start[[4]]]]],
		mergeRestriction[Rest[start], Append[end,start[[1]]]]
	]
]


reduce[stacks_]:=
Which[
	MatchQ[Last[stacks[[2]]],CcsSum[_,_]],
	{Append[Most[Most[stacks[[1]]]],CcsSum[stacks[[1,-2]],stacks[[1,-1]]]],Most[stacks[[2]]]},

	MatchQ[Last[stacks[[2]]],CcsPar[_,_]],
	{Append[Most[Most[stacks[[1]]]],CcsPar[stacks[[1,-2]],stacks[[1,-1]]]],Most[stacks[[2]]]},

	MatchQ[stacks[[2,-1]], ")"] && MatchQ[stacks[[2,-2]],"("],
	{stacks[[1]],Drop[stacks[[2]],-2]},

	MatchQ[Last[stacks[[2]]],CcsCat[_,_]],
	{Append[Most[stacks[[1]]],CcsCat[stacks[[2,-1,1]], stacks[[1,-1]]]],Most[stacks[[2]]]},


	MatchQ[Last[stacks[[2]]],CcsRes[_,_]],
	{Append[Most[stacks[[1]]],CcsRes[stacks[[2,-1,1]], stacks[[1,-1]]]],Most[stacks[[2]]]},

	MatchQ[Last[stacks[[2]]], "$"],
	{stacks[[1]],Most[stacks[[2]]]}
]


parse[tokens_, stacks_]:=
Which[
	Length[tokens]==0,
	If[Length[stacks[[2]]]==0,
		{tokens, stacks},
		If[MatchQ[Last[stacks[[2]]],"$"],
			{tokens, stacks},
			parse[{},reduce[stacks]]
		]
	],

	MatchQ[tokens[[1]],"0"] || MatchQ[tokens[[1]],CcsIde[_]],
	parse[Rest[tokens],{Append[stacks[[1]],tokens[[1]]],stacks[[2]]}],

	MatchQ[tokens[[1]], CcsSum[_,_]],
	If[MatchQ[Last[stacks[[2]]],"("]|| MatchQ[Last[stacks[[2]]],"$"],
		parse[Rest[tokens],{stacks[[1]],Append[stacks[[2]],CcsSum["_","_"]]}],
		parse[tokens,reduce[stacks]]
	],

	MatchQ[tokens[[1]], CcsPar[_,_]],
	If[MatchQ[Last[stacks[[2]]],CcsSum[_,_]]|| MatchQ[Last[stacks[[2]]],"("]||  MatchQ[Last[stacks[[2]]],"$"],
		parse[Rest[tokens],{stacks[[1]],Append[stacks[[2]],CcsPar["_","_"]]}],
		parse[tokens,reduce[stacks]]
	],

	MatchQ[tokens[[1]], "("],
	If[MatchQ[Last[stacks[[2]]],")"],
		Print["error. missing operator"],
		parse[Rest[tokens],{stacks[[1]],Append[stacks[[2]],"("]}]
	],

	MatchQ[tokens[[1]], ")"],
	If[MatchQ[Last[stacks[[2]]],"$"],
		Print["error. unbalanced right parenthesis"],
		If[MatchQ[Last[stacks[[2]]],"("],
			parse[Rest[tokens],{stacks[[1]],Append[stacks[[2]],")"]}],
			parse[tokens,reduce[stacks]]
		]
	],

	MatchQ[tokens[[1]], "$"],
	If[MatchQ[stacks[[2,-1]],"("],
		Print["error. missing right parenthesis"],
		If[MatchQ[stacks[[2,-1]],"$"],
		{tokens, stacks},
		parse[tokens,reduce[stacks]]
		]
	],

	MatchQ[tokens[[1]], CcsCat[_,_]] ,
	If[MatchQ[Last[stacks[[2]]],")"],
		parse[tokens,reduce[stacks]],
		parse[Rest[tokens],{stacks[[1]],Append[stacks[[2]],tokens[[1]]]}]
	],

	MatchQ[tokens[[1]], CcsRes[_,_]],
	If[MatchQ[stacks[[2,-1]],")"] (*|| MatchQ[stacks[[2,-1]],CcsCat[_,_]]*),
		parse[tokens,reduce[stacks]],
		parse[Rest[tokens],{stacks[[1]],Append[stacks[[2]],CcsRes[tokens[[1,1]],"_"]]}]
	]
]


ccsParseProcess[process_]:=
parse[
	ToSyntNode[
		Append[
			mergeRestriction[
				mergeActionWithDot[
					Select[
						Map[
							StringTrim,
							StringSplit[process,x:"."|"+"|"("|")"|"|"|"/"|"{"|"}":>x]
						],
						Not[MatchQ["",#]]&
					],
					{}
				],
				{}
			],
			"$"
		],
		{}
	][[2]],
	{{"$"},
	{"$"}}
][[2,1,2]]


(*prende una stringa che contiene una sequenza di definizione di identificatore separate da punto e virgola, 
	e restituisce una lista di coppie (identificatore, processo che lo definisce)*)
parseDefinitions[defs_]:=
	Map[StringTrim,Map[StringSplit[#,"="]&,StringSplit[defs,{";",","}]],2]


(*syntTree e' l'albero sintattico di un processo CCS, consts e' una sequenza di definizioni di identificatori.
	questa funzione calcola una parte della semantica di syntTree, in particolare restituisce solo gli archi che 
	partono dal nodo etichettato syntTree. Chiameremo questa parte della semantica, semantica monopasso di syntTree
*)
SingleStepTransition[syntTree_, consts_]:=
Which[
	
	MatchQ[syntTree, Null],
	{},

	(* se il processo e' 0 allora non ci sono archi*)
	MatchQ[syntTree, "0"],
	{},

	(* se il processo e' un identificatore A allora la funzione si chiama ricorsivamente sul processo P che definisce A
		e poi all'interno della semantica restituita dalla chiamata ricorsiva, sostituisce l'identificatore A al
		processo P*)
	MatchQ[syntTree, CcsIde[_]],
	identifierDefinition = Select[consts, MatchQ[#, {Part[syntTree,1],_}]&];
	If[Length[identifierDefinition]!=1, Print["identifier ", syntTree[[1]], " undefined"]; Abort[]];
	constDefinition:=ccsParseProcess[identifierDefinition[[1,2]]];
	Map[
		If[MatchQ[Part[#,1,1],constDefinition],
			{syntTree->Part[#,1,2],Part[#,2]},
			#
		]&,
		SingleStepTransition[constDefinition, consts]
	],


	(* se il processo e' un prefisso label.P allora restituisce solo l'arco  {(a.P) Overscript[\[LongRightArrow], a] P}*)
	MatchQ[syntTree, CcsCat[_,_]],
	{{syntTree->Part[syntTree,2],Part[syntTree,1]}},


	(* se il processo e' una somma P+Q allora la funzione si chiama ricorsivamente su P e su Q.
		Se le chiamate ricorsive restituiscono rispettivamente gli insiemi di archi E ed F allora 
		la funzione calcola
			{((P+Q), label, R), dove (P, label, R) \[Element] E}
 			\[Union] {((P+Q), label, R) dove (Q, label, R) \[Element] F}
	*)
	MatchQ[syntTree, CcsSum[_,_]],
	Join[
		Map[
			If[MatchQ[Part[#,1,1],Part[syntTree,1]],
				{syntTree->Part[#,1,2],Part[#,2]},
				#
			]&,
			SingleStepTransition[Part[syntTree, 1], consts]
		],
		Map[
			If[MatchQ[Part[#,1,1],Part[syntTree,2]],
				{syntTree->Part[#,1,2],Part[#,2]},
				#
			]&,
			SingleStepTransition[Part[syntTree, 2], consts]
		]
	],

	(* se il processo e' una composizione parallela P|Q allora la funzione si chiama ricorsivamente su P e su Q. 
		Se le chiamate ricorsive restituiscono rispettivamente gli insiemi di archi E ed F allora la funzione calcola
			{((P|Q), label, (R|S)), dove (P, label, R) \[Element] E e T \[Element] M} 
			\[Union] {((P|Q), label, (R|S)), dove (Q, label, S) \[Element] F e T \[Element] N}
		*)
	MatchQ[syntTree, CcsPar[_,_]],
	Join[
		Map[
			If[MatchQ[Part[#,1,1],Part[syntTree,1]],
				{syntTree->CcsPar[Part[#,1,2], Part[syntTree, 2]],Part[#,2]},
				#
			]&,
			SingleStepTransition[Part[syntTree, 1], consts]
		],
		Map[
			If[MatchQ[Part[#,1,1],Part[syntTree,2]],
				{syntTree->CcsPar[Part[syntTree,1],Part[#,1,2]],Part[#,2]},
				#
			]&,
			SingleStepTransition[Part[syntTree, 2], consts]
		]
	],


	(* se il processo e' una restrizione seguita immediatamente da una composizione parallela Restr/(P|Q) allora la 
		funzione si  chiama ricorsivamente su P e su Q. Se le chiamate ricorsive restituiscono rispettivamente gli 
		insiemi di archi E ed F allora la funzione calcola:
		{((Restr/(P|Q)), label, Restr/(R|Q))), dove (P, label, R) \[Element] E e label\[NotElement]Restr} 
			\[Union] {((Restr/(P|Q)), label, (Restr(P|R))), dove (Q, label, R) \[Element] F label\[NotElement]Restr} 
			\[Union] {((Restr/(P|Q)), tau, (Restr(R|T))), dove (P, a, R) \[Element] E e (Q, :a, T) \[Element] F e a\[Element]Restr} 
			\[Union] {((Restr/(P|Q)), tau, (Restr(R|T))), dove (P, :a, R) \[Element] E e (Q, a, T) \[Element] F e a\[Element]Restr}
	*)
	MatchQ[syntTree, CcsRes[_,CcsPar[_,_]]],
	semP = SingleStepTransition[Part[syntTree,2, 1],consts];
	semQ = SingleStepTransition[Part[syntTree,2, 2],consts];
	Join[
		Map[
			{CcsRes[Part[syntTree,1],CcsPar[Part[#,1,1],Part[syntTree,2,2]]]->CcsRes[Part[syntTree,1],CcsPar[Part[#,1,2],Part[syntTree,2,2]]],Part[#,2]}&,
			Select[
				semP,
				If[MatchQ[Part[#,2],CcsCom[_]], 
					Not[MemberQ[Part[syntTree,1],Part[#,2,1,1]]], 
					Not[MemberQ[Part[syntTree,1],Part[#,2,1]]]
				]&
			]
		],
		Map[
			{CcsRes[Part[syntTree,1],CcsPar[Part[syntTree,2,1], Part[#,1,1]]]->CcsRes[Part[syntTree,1],CcsPar[Part[syntTree,2,1],Part[#,1,2]]],Part[#,2]}&,
			Select[
				semQ,
				If[MatchQ[Part[#,2],CcsCom[_]], 
					Not[MemberQ[Part[syntTree,1],Part[#,2,1,1]]], 
					Not[MemberQ[Part[syntTree,1],Part[#,2,1]]]
				]&
			]
		],
		Select[
			Flatten[
				Outer[
					If[MatchQ[Part[#1,2],CcsCom[Part[#2,2]]]||MatchQ[Part[#2,2],CcsCom[Part[#1,2]]],
						{CcsRes[Part[syntTree,1],CcsPar[Part[#1,1,1], Part[#2,1,1]]]->CcsRes[Part[syntTree,1],CcsPar[Part[#1,1,2],Part[#2,1,2]]],"tau"},
						Null
					]&,
					Select[
						semP,
						If[MatchQ[Part[#,2],CcsCom[_]], 
							MemberQ[Part[syntTree,1],Part[#,2,1,1]], 
							MemberQ[Part[syntTree,1],Part[#,2,1]]
						]&
					],
					Select[
						semQ,
						If[MatchQ[Part[#,2],CcsCom[_]], 
							MemberQ[Part[syntTree,1],Part[#,2,1,1]], 
							MemberQ[Part[syntTree,1],Part[#,2,1]]
						]&
					],
					1
				],
				1
			],
			Not[MatchQ[#,Null]]&
		]
	],


	
	(* se il processo e' una restrizione Restr/P, dove P non e' una composizione parallela allora la 
		funzione si chiama ricorsivamente su P. Se le chiamate ricorsiva restituisce l'insieme di archi E
		allora la funzione calcola:
				{((Restr/P), a,(Restr/Q)), dove (P, a, Q) \[Element] E e a \[NotElement] Restr}
	*)
	MatchQ[syntTree, CcsRes[_,_]] && Not[MatchQ[syntTree, CcsRes[_,CcsPar[_,_]]]],
	Map[
		{CcsRes[Part[syntTree,1], Part[#, 1,1]]-> CcsRes[Part[syntTree,1], Part[#, 1,2]], Part[#, 2]}&,
		Select[SingleStepTransition[Part[syntTree,2],consts],Not[MemberQ[Part[syntTree,1], Part[#,2,1]]]&]
	],

	True,
	Print["error. \n\t syntTree: ",syntTree,"\n\t definitions: ",consts];
]


(*questa funzione retistuisce la coppia:
	1. unione dei primi due argomenti
	2. semantica monopasso di tutti i processi contenuti in newTransitions
*)
ApplySingleStepTransition[graph_,newTransitions_, consts_]:=
{
	DeleteDuplicates[
		Join[
			graph,
			Select[
				newTransitions,
				Not[MatchQ[#,{}]]&
			]
		]
	],
	Flatten[
		Map[
			SingleStepTransition[#,consts]&,
			DeleteDuplicates[Map[Part[#,1,2]&,newTransitions]]
		],
		1
	]
}


(*questa funzione prende in input un albero sintattico di un processo CCS,
	e restituisce la stringa che rappresenta il processo CCS*)
ccsSyntTreeToExpr[x_]:=
	Which[

	MatchQ[x,"0"]||MatchQ[x,"tau"],
	Return[x],

	MatchQ[x,CcsAct[_]],
	Return[StringForm["``",x[[1]]]],

	MatchQ[x,CcsCom[_]],
	Return[StringForm[":``",x[[1]][[1]]]],

	MatchQ[x,CcsCat[_,_]],
	Return[StringForm["``.``",ccsSyntTreeToExpr[x[[1]]],ccsSyntTreeToExpr[x[[2]]]]],
 
	MatchQ[x,CcsSum[_,_]],
	Return[StringForm["(`` + ``)",ccsSyntTreeToExpr[x[[1]]],ccsSyntTreeToExpr[x[[2]]]]],

	MatchQ[x,CcsPar[_,_]],
	Return[StringForm["(`` | ``)",ccsSyntTreeToExpr[x[[1]]],ccsSyntTreeToExpr[x[[2]]]]],

	MatchQ[x,CcsRes[_,_]],
	Return[StringForm["(`` / ``)",x[[1]],ccsSyntTreeToExpr[x[[2]]]]],

	MatchQ[x,CcsIde[_]],
	Return[x[[1]]],

	True,
	Print["ccsSyntTreeToExpr: Syntax error in: ",x];
	Return[Null]
	]


(* calcola la semantica del processo ccs rappresentato dalla stringa ccsProcess.
	constantsDefinition e' una stringa che contiene una sequenza di definizioni di 
	identificatori separate da punto e virgola.
	La funzione chiama ripetutamente ApplySingleStepTransition su:
	1. un grafo inizialmente vuoto
	2. la semantica monopasso di ccsProcess
	fino a quando il primo grafo non si stabilizza.  
*)
getCcsGraph[ccsProcess_,constantsDefinition_, step_]:=
	Map[
		{ccsSyntTreeToExpr[Part[#,1,1]]->ccsSyntTreeToExpr[Part[#,1,2]], ccsSyntTreeToExpr[Part[#,2]]}&,
		FixedPoint[
			ApplySingleStepTransition[Part[#,1],Part[#,2],parseDefinitions[constantsDefinition]]&,		
			{{}, SingleStepTransition[ccsParseProcess[ccsProcess],parseDefinitions[constantsDefinition]]},
			step
		][[1]]
	]


End[]


EndPackage[]
