:- module(asymptoticplp,[
                        compute_lp_form/3,
                        compute_lp_form/4,
                        compute_lfp_form/2,
                        reduced_quant_elim/2,
                        compute_lp_lfp/3,
                        compute_lp_lfp/4,
                        datalog_to_formula/2,
                        datalog_to_formula/3
                        ]).
:- use_module(library(pairs)).
:- use_module(library(lists)).
:- use_module(library(ordsets)).
:- use_module(library(apply)).
:- use_module(library(occurs)).
:- use_module(library(terms)).
:- use_module(library(clpfd)).
:- use_module(library(occurs)).

:- op(800, yfx, and).
:- op(700, yfx, or).

/* Predicates offered:
 * compute_lp_form/3
 * compute_lp_form/4
 * compute_lfp_form/2
 * reduced_quant_elim/2
 * compute_lp_lfp/3
 * compute_lp_lfp/4
 * datalog_to_formula/2
 * datalog_to_formula/3,
 *  */


/* A clause is represented as a pair Head-Body, where Body is a list of literals.
 * A literal is represented as a pair of a predicate symbol and a list of terms
 * A Datalog formula is represented as a pair (Pi-P), where Pi is a list of clauses, P a predicate.
 * Subvars is nested list of variables used to substitute variables when needed
 * An slfp formula is represented as slfp(list of predicates, list of formulas,Variables)*/

/* datalog_to_formula(+Datalog formula, -equivalent slfp formula) */
datalog_to_formula(Datalog,SLFP) :-
    datalog_to_formula(Datalog,[a,b,c,d,e,f,g,h],SLFP).
/* datalog_to_formula(Datalog(+Datalog formula, +list of variables to be substituted, -equivalent slfp formula */
 datalog_to_formula(Datalog, Subvars, slfp(Preds,ReducedPhis,FreeVars)) :-
  Datalog = Pi-P,
  intentionals(Pi, Ipreds),
  do_substitution(Pi, Ipreds, Subvars, NewPi),
  ord_subtract(Ipreds,[P],Ipreds_aux),
  Preds = [P|Ipreds_aux],
  getFreeVarsInRightOrder(Preds,NewPi, FreeVars),
  maplist(program_to_formula(NewPi),Preds,Phis),
  maplist(reduced_form, Phis, ReducedPhis).

/* getFreeVarsInRightOrder(+predicates,+program,-free variables) */
getFreeVarsInRightOrder([], _, []).
getFreeVarsInRightOrder([FirstPred|RestPred], Clauses, RightFreevars) :-
    include(checkHeadPred(FirstPred), Clauses, PredClauses),
    getAllHeads(PredClauses, Heads),
    sort(Heads, SortedHeads),
    maplist(variables_in_literal, SortedHeads, FreeVars),
    append(FreeVars, Out, RightFreevars),
    getFreeVarsInRightOrder(RestPred, Clauses, Out).


/* program_to_formula1(+Predicate Q,+Clauses,-formula phi_Q) */
program_to_formula1(_,[],false).
program_to_formula1(Q,[Head-Body|Clauses],F or Fs) :-
    Head = Q-_,
    clause_to_formula(Head-Body,F),
    program_to_formula1(Q,Clauses, Fs).
program_to_formula1(Q,[Head-_|Clauses],F) :-
    Head \= Q-_,
    program_to_formula1(Q,Clauses, F).

/* program_to_formula(+ Clauses,+ Predicate Q,-formula phi_Q) */
program_to_formula(Program,Q,Phi) :-
    program_to_formula1(Q,Program,Phi).

/* conjoin_body(+Body,-Conjunct of literals) */
conjoin_body([],[]).
conjoin_body(Parts,Conj and true) :-
    Parts \= [],
    maplist(term_to_atom,Parts, AtomicTerm),
    atomic_list_concat(AtomicTerm, ' and ', AtomicConjunction),
    term_to_atom(Conj, AtomicConjunction).

/* clause_to_formula(+Clause, -Disjunct of phi_Headpredicate corresponding to Clause) */
clause_to_formula(Head-Body,Psi) :-
    include(atom, Body, AtomsInBody),
    AtomsInBody == [],
    variables_free_in_body(Head-Body,Freevars),
    clause_to_formula_aux(Head-Body,Freevars,Psi).

/* clause_to_formula(+Clause, -the constant of phi_Headpredicate corresponding to clause) */
clause_to_formula(Head-Body,Psi) :-
    include(atom, Body, AtomsInBody),
    AtomsInBody \= [],
    clause_to_formula_aux(Head-Body,[],Psi).

/* clause_to_formula_aux(+Head-Body,+variables, -constant of phi_Headpredicate) */
clause_to_formula_aux(_-Body,Freevars,exists(Freevars,Psi)) :-
    conjoin_body(Body,Psi).

/* variables_in_body(+Clause, -variables in the clause) */
variables_in_body(Body,Vars) :-
    maplist(extract_inner_literal, Body, PosBody),
    pairs_values(PosBody, Varss),
    append(Varss,Varsdupl),
    sort(Varsdupl,Vars).

/* variables_in_body_unsorted(+Clause,-variables in the clause */
variables_in_body_unsorted(Body,Varsdupl) :-
    maplist(extract_inner_literal, Body, PosBody),
    pairs_values(PosBody, Varss),
    append(Varss,Varsdupl).

/* variables_in_literal(+literal,-variables) */
variables_in_literal(_-Vars,Vars) :-
    Vars \= not(_).
variables_in_literal(not(X),Vars) :-
    variables_in_literal(X,Vars).

/* variables_free_in_body(+clause,-variables) */
variables_free_in_body(Head-Body,Vars) :-
    variables_in_literal(Head,Headvars1),
    variables_in_body(Body,Bodyvars1),
    sort(Headvars1, Headvars),
    sort(Bodyvars1, Bodyvars),
    ord_subtract(Bodyvars,Headvars,Vars).

/* extract_inner_literal(+literal,-atom) */
extract_inner_literal(not(X), X).
extract_inner_literal(X,X) :-
    X \= not(_).

/* intentionals(+Clauses, -heads occuring in a clause) */
intentionals(Clauses,Headpreds) :-
    pairs_keys(Clauses,Heads),
    pairs_keys(Heads,Headpredsdupl),
    sort(Headpredsdupl,Headpreds).

/* bodyPreds(+Clauses, -preds occuring in a clause body but are not head of a clause) */
bodyPreds(Clauses,BodyHeads) :-
    pairs_values(Clauses, Bodies),
    flatten(Bodies, FlatBody),
    maplist(extract_inner_literal, FlatBody, BodiesDupl),
    sort(BodiesDupl, Bodypreds),
    pairs_keys(Bodypreds, BodyHeads).

/* We collate some trivial reduction steps to avoid overfreighting our formulas */
/* reducible(+formula) */
:- discontiguous reducible/1.
/* reduction_step(+formula,-reduced formula */
:- discontiguous reduction_step/2.

%reduction_step(Phi,Phi) :-
%   getLiteral(Phi).

reduction_step(exists([],Phi),Phi) :- !.
reducible(exists([],_)).

reduction_step(forall([],Phi),Phi) :- !.
reducible(forall([],_)).

reduction_step(exists(Vars,Phi),exists(Vars,Phi_r)) :-
    Phi \= false,
    Phi \= true,
    reduction_step(Phi, Phi_r),!.
reduction_step(forall(Vars,Phi),forall(Vars,Phi_r)) :-
    Phi \= false,
    Phi \= true,
    reduction_step(Phi, Phi_r),!.
reducible(exists(_,Phi)) :-
          reducible(Phi).
reducible(forall(_,Phi)) :-
          reducible(Phi).

reduction_step(exists(_,false), false) :- !.
reduction_step(exists(_,true), true):- !.
reduction_step(forall(_,false), false):- !.
reduction_step(forall(_,true), true):- !.


reducible(exists(_,false)).
reducible(exists(_,true)).
reducible(forall(_,true)).
reducible(forall(_,false)).


reduction_step(false or Phi, Phi).
reduction_step(Phi or false, Phi).
reduction_step(false and _, false).
reduction_step(_ and false, false).
reducible(_ or false).
reducible(false or _).
reducible(_ and false).
reducible(false and _).

reduction_step(true or _, true).
reduction_step(_ or true, true).
reduction_step(true and Phi, Phi).
reduction_step(Phi and true, Phi).
reducible(_ and true).
reducible(true and _).
reducible(_ or true).
reducible(true or _).

reduction_step(not(Phi) and Phi, false) :- !.
reduction_step(Phi and not(Phi), false) :- !.
reducible(Phi and not(Phi)).
reducible(not(Phi) and Phi).

reduction_step(Phi and Phi, Phi) :- !.
reduction_step(Phi or Phi, Phi) :- !.
reducible(Phi and Phi).
reducible(Phi or Phi).

reduction_step(Phi and Psi,Phi_r and Psi) :-
    Phi \= Psi,
    reduction_step(Phi,Phi_r).
reduction_step(Phi and Psi,Phi and Psi_r) :-
    Phi \= Psi,
    reduction_step(Psi,Psi_r).
reducible(Phi and Psi) :-
    Phi \= Psi,
    (   reducible(Phi)
    ; reducible(Psi)
    ).

reduction_step(Phi or exists(_,false), Phi).
reduction_step(exists(_,false) or Phi, Phi).
reduction_step(_ and exists(_,false), false).
reduction_step(exists(_,false) and _, false).

reduction_step(Phi and exists(_,true), Phi).
reduction_step(exists(_,true) and Phi, Phi).
reduction_step(_ or exists(_,true), true).
reduction_step(exists(_,true) or _ , true).

reduction_step(Phi or forall(_,false), Phi).
reduction_step(forall(_,false) or Phi, Phi).
reduction_step(_ and forall(_,false), false).
reduction_step(forall(_,false) and _, false).

reduction_step(Phi and forall(_,true), Phi).
reduction_step(forall(_,true) and Phi, Phi).
reduction_step(_ or forall(_,true), true).
reduction_step(forall(_,true) or _ , true).

reduction_step(not(Phi) or Phi, Phi) :- !.
reduction_step(Phi or not(Phi), Phi) :- !.
reducible(Phi or not(Phi)).
reducible(not(Phi) or Phi).

reduction_step(Phi or Psi,Phi_r or Psi) :-
    reduction_step(Phi,Phi_r).

reduction_step(Phi or Psi,Phi or Psi_r) :-
    reduction_step(Psi,Psi_r).

reducible(Phi or Psi) :- reducible(Phi); reducible(Psi).

reduction_step(forall(_,_,Phi), Phi_r) :-
    reduction_step(Phi, Phi_r).
reducible(forall(_,_,_)).

reduction_step(exists(_,_,Phi), Phi_r) :-
    reduction_step(Phi, Phi_r).
reducible(exists(_,_,_)).

reducible(_ or exists(_,_,_)).
reducible(_ and exists(_,_,_)).
reducible(_ or forall(_,_,_)).
reducible(_ and forall(_,_,_)).

reducible(exists(_,_,_) or _).
reducible(exists(_,_,_) and _).
reducible(forall(_,_,_) or _).
reducible(forall(_,_,_) and _).


reduction_step(not(not(X)), X).
reducible(not(not(_))).

reduction_step(not(exists(BoundVars,Phi)), forall(BoundVars,not(Phi))).
reducible(not(exists(_,_))).

reduction_step(not(forall(BoundVars,Phi)), exists(BoundVars,not(Phi))).
reducible(not(forall(_,_))).


%reduces_to(Phi,Phi).
%reduces_to(Phi,Psi) :-
%    reduces_to(Phi,Chi),
%    reduction_step(Chi,Psi).
%reduced_form(Phi or false, Phi_r) :-
%    reduced_form(Phi, Phi_r),!.
%reduced_form(false or Phi, Phi_r) :-
%    reduced_form(Phi, Phi_r),!.
%reduced_form(_ or true, true) :- !.
%reduced_form(true or _, true) :- !.
%reduced_form(_ and false, false) :- !.
%reduced_form(false and _, false) :- !.

%reduced_form(Phi,Psi) :-
%    reduces_to(Phi,Psi),
%    \+reducible(Psi), !.

/* reduced_form(+Phi,-Chi) */
reduced_form(Phi,Chi) :-
  reduction_step(Phi,Psi),
  !,
  (   \+reducible(Psi)
  ->  Chi = Psi
  ;   reduced_form(Psi,Chi)).

reduced_form(Phi,Phi) :-
  \+reducible(Phi).

substitute_heads_body([],_,Head-Body,Head-Body).
substitute_heads_body(Vars,Terms,Head-Body,Head-ReplBody) :-
    Head = _-Headvars,
    Vars \= Headvars,
    variables_in_body_unsorted(Body,Bodyvars),
    intersection(Vars,Bodyvars,Intersec),
    unique(Vars),
    unique(Intersec),
    getIndexOfDupl1(Intersec, Vars, Inds),
    maplist(removetail, Inds, FirstInds),
    flatten(FirstInds, FlatInds),
    sort(FlatInds,SortedFlatInds),
    getElemWithGivenIndex(Terms, SortedFlatInds, RelvVars),
    replace_rec(Body,Intersec,RelvVars, ReplBody).
substitute_heads_body(Vars,Terms,Head-Body,Newhead-ReplBody) :-
    Head = P-Vars,
    Newhead = P-Terms,
    variables_in_body_unsorted(Body,Bodyvars),
    intersection(Vars,Bodyvars,Intersec),
    unique(Vars),
    unique(Intersec),
    getIndexOfDupl1(Intersec, Vars, Inds),
    maplist(removetail, Inds, FirstInds),
    flatten(FirstInds, FlatInds),
    sort(FlatInds,SortedFlatInds),
    getElemWithGivenIndex(Terms, SortedFlatInds, RelvVars),
    replace_rec(Body,Intersec,RelvVars, ReplBody).

substitute_heads_body(Vars,Terms,Head-Body,Newhead-NewBody) :-
    Head = P-Vars,
    Newhead = P-Terms,
    variables_in_body_unsorted(Body,Bodyvars),
    intersection(Vars,Bodyvars,Intersec),
    \+unique(Intersec),
    sort(Intersec, SortedIntersec),
    getIndexOfDupl1(SortedIntersec, Vars, Inds),
    maplist(removetail, Inds, FirstInds),
    flatten(FirstInds, FlatInds),
    getElemWithGivenIndex(Terms, FlatInds, RelvVars),
    replace_rec(Body,SortedIntersec,RelvVars, ReplBody),
    duplicates(Vars,Dupl),
    create_util_pred_same1(Vars, Dupl,Terms, SamePreds),
    append(ReplBody,SamePreds, NewBody).


/* Some predicates to deal with variables in formulas */
/* freevars(Formula, free variables) */
freevars(true,[]).
freevars(false,[]).
freevars(_-Vars,SortedVars) :-
  sort(Vars,SortedVars).
freevars(Phi and Psi, Vars) :-
    \+atom(Phi),
    \+atom(Psi),
    freevars(Phi,Phivars),
    freevars(Psi,Psivars),
    ord_union(Phivars,Psivars,Vars).
freevars(Phi and Psi, []) :-
    atom(Phi),
    atom(Psi).
freevars(Phi or Psi, Vars) :-
    \+atom(Phi),
    \+atom(Psi),
    freevars(Phi,Phivars),
    freevars(Psi,Psivars),
    ord_union(Phivars,Psivars,Vars).
freevars(Phi or Psi, Vars) :-
    atom(Phi),
    \+atom(Psi),
    freevars(Psi,Psivars),
    sort(Psivars, Vars).
freevars(Phi or Psi, Vars) :-
    \+atom(Phi),
    atom(Psi),
    freevars(Phi,Phivars),
    sort(Phivars, Vars).
freevars(exists(Boundvars,Phi),Vars) :-
    freevars(Phi,Phivars),
    subtract(Phivars,Boundvars,Vars).
freevars(forall(Boundvars,Phi),Vars) :-
    freevars(Phi,Phivars),
    subtract(Phivars,Boundvars,Vars).
freevars(lfp(_,Formula),FV) :-
    freevars(Formula, FV).
freevars(not(_-Vars), Vars).

getAllHeads(Clauses, Heads) :-
    pairs_keys(Clauses, Heads).

getFirst([First|_], First).

/* Flattens a list that consists only of one element*/
flatten1([],[]).
flatten1([L],L).

/* substituted clauses are replaced with first occurring head*/
getReplacer(Replacer1, [FirstClause|_]) :-
    getFirst([FirstClause|_], FirstClause),
    pairs_keys([FirstClause], Replacer),
    flatten1(Replacer, Replacer1).


checkHeadPred(HeadPred, P-_-_) :-
    HeadPred == P.

getLiteral(_-_).
getLiteral(not(_-_)).

checkPredLiteral(HeadPred, P-_) :-
    HeadPred == P.
checkPredLiteral(HeadPred, not(P-_)) :-
    HeadPred == P.


/* Clauses with the same Headpredicate get the same variables, and free variables
   in Body are substituted with index of the headpredicate*/
do_substitution(_, [], _, []).
do_substitution(Clauses, [FirstPred|Rest], SubVars, FinalNewClauses) :-
    include(checkHeadPred(FirstPred), Clauses, AllRelvClauses),
    getAllHeads(AllRelvClauses, Heads),
    getReplacer(Replacer, AllRelvClauses),
    variables_in_literal(Replacer, ReplacerVars),
    unique(ReplacerVars),
    maplist(variables_free_in_body, AllRelvClauses, FreeVars),
    length(FreeVars, LenFreeVars),
    length(SubVars, LenSubVars),
    copy_list([FirstPred], LenSubVars, EnoughPredIndices),
    maplist(atom_concat, SubVars, EnoughPredIndices, NewSubVars),
    copy_list([NewSubVars], LenFreeVars, EnoughSubVars),
    maplist(substitute_heads_body, FreeVars, EnoughSubVars, AllRelvClauses, SubstBodyClauseVars),
    maplist(variables_in_literal, Heads, OldHeadVars),
    length(OldHeadVars, LenOldHeadVars),
    copy_list([ReplacerVars], LenOldHeadVars, NewHeadVars),
    maplist(substitute_heads_body, OldHeadVars, NewHeadVars, SubstBodyClauseVars, NewClauses),
    append(NewClauses, Output, FinalNewClauses),
    do_substitution(Clauses, Rest, SubVars, Output),!.
do_substitution(Clauses, [FirstPred|Rest], SubVars, FinalNewClauses) :-
    include(checkHeadPred(FirstPred), Clauses, AllRelvClauses),
    getAllHeads(AllRelvClauses, Heads),
    getReplacer(Replacer, AllRelvClauses),
    variables_in_literal(Replacer, ReplacerVars),
    \+unique(ReplacerVars),
    sort(ReplacerVars, SortedReplacerVars),
    getIndexOfDupl(SortedReplacerVars, ReplacerVars, IndList),
    get_dupl_replacers(SortedReplacerVars, IndList, DuplRepl),
    maplist(removehead, IndList, RestIndList),
    maplist(removehead, DuplRepl, RestDuplRepl),
    repl_listwise_rec(ReplacerVars, RestIndList, RestDuplRepl, NewReplVars),
    maplist(variables_in_literal, Heads, OldHeadVars),
    length(OldHeadVars, LenOldHeadVars),
    copy_list([NewReplVars], LenOldHeadVars, NewHeadVars),
    maplist(substitute_heads_body, OldHeadVars,NewHeadVars, AllRelvClauses, NewClauses),
    append(NewClauses, Output, FinalNewClauses),
    do_substitution(Clauses, Rest, SubVars, Output),!.

/* Given Head and Body, this predicate forms a literal of Head-Body */
put_together(Head, Body, Head-Body).


/* Replicates element in list times N */
copy_list(L, N, Copies) :-
    length(Lists, N),           % List of length N
    maplist(=(L), Lists),       % Each element of Lists is unified with L
    append(Lists, Copies).      % Lists is flattened

/* Adds the lfp-constructor to formulas if necessary */
build_lfp_constructor(Pred, exists(Boundvars, Phi), lfp(Pred, exists(Boundvars, Phi))) :-
    contains_term(Pred,Phi).
build_lfp_constructor(Pred, forall(Boundvars, Phi), lfp(Pred, forall(Boundvars, Phi))) :-
	contains_term(Pred,Phi).
build_lfp_constructor(Pred, Phi, lfp(Pred, Phi)) :-
    contains_term(Pred,Phi),
    Phi \= exists(_,_),
    Phi \= forall(_,_).
build_lfp_constructor(Pred, Phi, Phi) :-
    \+contains_term(Pred,Phi).

/* Auxilary predicate to get the freevars of a lfp-formula */
getFreeVarsOfFormula(Phi, Freevars) :-
    Phi \= lfp(_,_),
    freevars(Phi, Freevars).
getFreeVarsOfFormula(lfp(_, Phi), Freevars) :-
    freevars(Phi, Freevars).

/*Auxilary predicate to check if it is a subatom*/
sub_atom1(Subatom, Atom) :-
    sub_atom(Atom,_,_,_,Subatom).

/* Extracts the headpredicate of a literal */
pred_in_literal(Pred-_, Pred).

/* Used to check if a formula contains the lfp-constructor */
is_lfp_formula(lfp(_,_)).

/* Gets the max arity of relevant predicates in a lfp-formula */
getHighestArityOfPreds(lfp(_, Formula), Max) :-
    findall(Value, sub_term(Value, Formula), SubTermList),
	include(getLiteral, SubTermList, Literals),
    sort(Literals, SortedLiterals),
    extract_inner_literals(lfp([_], Formula), InnerLiterals),
    subtract(SortedLiterals, InnerLiterals, RelvLiterals),
    maplist(variables_in_literal, RelvLiterals, Vars),
    maplist(length, Vars, Lens),
    max_list1(Lens, Max).

/* Because max_list fails for empty list */
max_list1([],0).
max_list1(List, Max) :-
    max_list(List,Max).

/* Gets all predicate-terms a lfp-formula contains */
getLiteralsFromLfp(lfp(_, Formula), Literals) :-
    findall(Value, sub_term(Value, Formula), SubTermList),
	include(getLiteral, SubTermList, Literals).

/* Gets the number of predicates a lfp-formula contains */
countAllPreds(lfp(_, Formula), LenPreds) :-
    findall(Value, sub_term(Value, Formula), SubTermList),
	include(getLiteral, SubTermList, Literals),
    sort(Literals, SortedLiterals),
    extract_inner_literals(lfp([_], Formula), InnerLiterals),
    subtract(SortedLiterals, InnerLiterals, RelvLiterals),
    maplist(pred_in_literal, RelvLiterals, Preds),
    sort(Preds, SortedPreds),
    length(SortedPreds, LenPreds).

/* Used to find all literals in a lfp-formula */
extract_inner_literals(lfp(_, Formula), SortedFlattend) :-
    Inners = lfp(_,_),
    findall(Inners, sub_term(Inners, Formula), SubTermList),
    maplist(getLiteralsFromLfp, SubTermList, LiteralsList),
    flatten(LiteralsList, Flattend),
    sort(Flattend, SortedFlattend).

/* Used to extract the bound variables */
extract_bound_vars(exists(Boundvars,_), Boundvars).
extract_bound_vars(forall(Boundvars,_), Boundvars).

/* Get all bound variables in a formula */
getBoundVarsOfFormula(Formula, SortedBoundvars) :-
    findall(Value, sub_term(Value, Formula), SubTermList),
    include(is_quantifier_formula,SubTermList, AllQuantFormulas),
    sort(AllQuantFormulas, Sorted),
    maplist(extract_bound_vars, Sorted, Boundvars),
    flatten(Boundvars, FlattenedBoundvars),
    sort(FlattenedBoundvars, SortedBoundvars).

/* Get free variables of a lfp-formula */
freeVarsOfLfp(lfp(_, Formula), Frees) :-
    getFreeVarsOfFormula(Formula, Frees).

/* Get all lfp-formulas including the nested ones */
getAllLfpFormulasOfAFormula(Formula, AllLfps) :-
    findall(Value, sub_term(Value, Formula), SubTermList),
    include(is_lfp_formula,SubTermList, AllLfps).

/* Getting the free vars that are not in inner lfp-formulas */
real_freevars([], _, []).
real_freevars([First|Rest], Boundvars, Output) :-
    subtract(First,Boundvars, FirstFreevars),
    Result = [FirstFreevars],
    append(Result,Out, Output),
    real_freevars(Rest, Boundvars, Out).

/* Computes the value alpha for the iteration stage formation rule: 2**(LenPreds*(LenFreevars**MaxArity))*/
countPredsFreeVarsArity(AllLfps,Boundvars,Alphas) :-
    maplist(countAllPreds, AllLfps, LenPreds),
    maplist(getHighestArityOfPreds, AllLfps, MaxArity),
    maplist(freeVarsOfLfp, AllLfps, MaybeFreevars),
	real_freevars(MaybeFreevars, Boundvars, Freevars),
    maplist(length, Freevars, LenFreevars),
    maplist(pow,LenFreevars,MaxArity,Result),
    maplist(mult,LenPreds,Result, Exp),
    length(Exp, LenForCompAlpha),
    copy_list([2], LenForCompAlpha, Base),
    maplist(pow,Base,Exp,Alphas).

mult(X,Y,R) :-
    R is X*Y.

/* Computes the new alpha constructor*/
compute_alpha(Formula, AllLfps, Boundvars, AtomAlphas1) :-
    getAllLfpFormulasOfAFormula(Formula, AllLfps),
    getBoundVarsOfFormula(Formula, Boundvars),
    countPredsFreeVarsArity(AllLfps, Boundvars, Alphas),
    maplist(atom_number, AtomAlphas, Alphas),
    maplist(atom_concat(alpha_),AtomAlphas,AtomAlphas1).

/* Replace former lfp-constructor with a new constructor */
replace_lfps(Formula,[],Formula).
replace_lfps(Formula, [First|Rest], NewFormula) :-
    term_to_atom(Formula, AtomFormula),
    nth1(Index,[First|Rest], First),
    replace_nth_word(AtomFormula,Index,lfp, First, InterResult),
    term_to_atom(Term,InterResult),
    replace_lfps(Term, Rest, NewFormula),!.


/* Auxilary predicate to replace the nthOccurence of ToReplace in Word with ReplaceWith */
replace_nth_word(Word,NthOcurrence,ToReplace,ReplaceWith,Result) :-
    call_nth(sub_atom(Word,Before,_Len,After,ToReplace),NthOcurrence),
    sub_atom(Word,0,Before,_,Left), % get left part
    sub_atom(Word,_,After,0,Right), % get right part
    atomic_list_concat([Left,ReplaceWith,Right],Result).

replace_nth_word_rec(Word,_,[], [], Word).
replace_nth_word_rec(Word,NthOcurrence,[FirstToRepl|RestToReplace], [FirstReplWith|RestReplWith], Result) :-
    call_nth(sub_atom(Word,Before,_Len,After,FirstToRepl),NthOcurrence),
    sub_atom(Word,0,Before,_,Left), % get left part
    sub_atom(Word,_,After,0,Right), % get right part
    atomic_list_concat([Left,FirstReplWith,Right],InterimResult),
    replace_nth_word_rec(InterimResult, NthOcurrence, RestToReplace, RestReplWith, Result).

/* Auxilary predicate to replace in a term without transforming it into an atom
 * Subterm0: will be replaced
 * Subterm: is the replacer
 * Term0: old term
 * Term: new term which contains Subterm now */
replace(Subterm0, Subterm, Term0, Term) :-
        (   Term0 == Subterm0 -> Term = Subterm
        ;   var(Term0) -> Term = Term0
        ;   Term0 =.. [F|Args0],
            maplist(replace(Subterm0,Subterm), Args0, Args),
            Term =.. [F|Args]
        ).

/*Does Iter iterations of
 * Insert PrevResult for the Literal
 * Old Boundvars will be replaced with new ones
 * The PrevResult is put on the end of NewResult
 * NewResult should be reduced as much as possible
 * To avoid doing too many unecessary iterations after each iteration quantifier elimination is done
 * To avoid endless disjunctions there is the terminate_isfr function which includes the notsat function */
isfr1(0,_,_,_,Term,ReducedTerm) :-
    %reduced_form(Term, ReducedTerm).
    reduced_quant_elim(Term, ReducedTerm).
isfr1(Iter, Counter, Term, Pred, PrevResult, NewResult) :-
    Iter > 0,
    Counter >= 0,
    NewIter is Iter - 1,
    NewCounter is Counter + 1,
    reduced_form(PrevResult, ReducedPrevResult),
    getBoundVarsOfFormula(Term, Boundvars),
    length(Boundvars, LenBoundvars),
    copy_list([NewCounter], LenBoundvars, EnoughIterIndices),
    maplist(atom_concat, Boundvars, EnoughIterIndices, NewBoundvars),
    freevars(ReducedPrevResult, FreevarsPrevResult),
    flatten1(Pred,FlatPred),
    find_relv_literal(Term, FlatPred, Literal),
    Literal \= [],
    variables_in_literal(Literal, LiteralVars),
    replace_vars(Boundvars, NewBoundvars, ReducedPrevResult,NewPrevResult),
    replace_rec(NewPrevResult,FreevarsPrevResult,LiteralVars,NewPrevResult1),
    term_to_atom1(Term, AtomFormula),
    term_to_atom1(Literal, AtomLiteral),
    term_to_atom1(NewPrevResult1, AtomNewPrevResult),
    replace_nth_word(AtomFormula,1,AtomLiteral, AtomNewPrevResult, InterResult),
    term_to_atom(ReplacedTerm, InterResult),
    reduced_form(ReplacedTerm, ReducedTerm),
    reduced_quant_elim(ReducedTerm, ReducedQuantTerm),
    transform_term(ReducedPrevResult, ReducedQuantTerm, TransfTerm),
    (   terminate_isfr(TransfTerm)
    ->  NewResult = ReducedQuantTerm
    ;   isfr1(NewIter, NewCounter, Term, Pred, ReducedQuantTerm or ReducedPrevResult, NewResult)
    ), !.
isfr1(Iter, Counter, Term, Pred, _, ReducedQuantTerm) :-
    Iter > 0,
    Counter >= 0,
    reduced_form(Term, ReducedTerm),
    reduced_quant_elim(ReducedTerm, ReducedQuantTerm),
    flatten1(Pred, FlatPred),
    find_relv_literal(Term, FlatPred, Literal),
    Literal == [].

/* This is added since running the program locally does not add spacing for false and true if they are
 *  transformed into an atom*/
term_to_atom1(false, 'false ').
term_to_atom1(true, 'true ').
term_to_atom1(Term, Res) :-
    Term \= false,
    Term \= true,
    term_to_atom(Term, Res).

/* Auxilary predicate to replace list of variables */
replace_vars(_,_,false,false) :- !.
replace_vars([],_,Term,Term) :- !.
replace_vars([FirstVars|RestVars], [FirstNVars|RestVars], Term, NewTerm) :-
    replace(FirstVars, FirstNVars, Term, FirstNewTerm),
    replace_vars(RestVars, RestVars, FirstNewTerm, NewTerm).

/* Auxilary predicate to find relevant literals in a term */
find_relv_literal(Term,Pred, Literal) :-
    findall(Value, sub_term(Value, Term), SubTermList),
    include(getLiteral, SubTermList, Literals),
    include(checkPredLiteral(Pred), Literals, RelvLiteral),
    member(Literal, RelvLiteral).

/* Extracts the IterNumber of the Alpha constructor */
get_iter_numbers([],[]).
get_iter_numbers([FirstAlpha|RestAlpha],Iterations) :-
    split_string(FirstAlpha, "_", "", Split),
    subtract(Split, ["alpha"], Result),
    flatten1(Result, IterString),
    number_string(IterNumber, IterString),
    append([IterNumber], Out, Iterations),
    get_iter_numbers(RestAlpha, Out).

getInnerFormula(exists(_,Formula), Formula).
getInnerFormula(forall(_,Formula), Formula).


is_quantifier_formula(forall(_,_)).
is_quantifier_formula(exists(_,_)).

getAllQuantifierFormulas(Formula, AllQuantFormulas) :-
    findall(Value, sub_term(Value, Formula), SubTermList),
    include(is_quantifier_formula,SubTermList, AllQuantFormulas).

seperate_elems_in_a_list([],[]).
seperate_elems_in_a_list([First|Rest], Res) :-
    Elem = [[First]],
    append(Elem, Out, Res),
    seperate_elems_in_a_list(Rest, Out).

/* Split term at 'and' or 'or' */
split_term(Phi or Psi, [Phi_r, Psi_r]) :-
   split_term(Phi, Phi_r),
    split_term(Psi, Psi_r),!.
split_term(Phi and Psi, [Phi_r, Psi_r]) :-
     split_term(Phi, Phi_r),
    split_term(Psi, Psi_r),!.
split_term(Phi,[Phi]) :-
    \+sub_term(or, Phi),
    \+sub_term(and, Phi).

/* First step of quantor elimination
 * For all variables which are not bound replace the bound variable with it and add it as a disjunction
 * to the formula if the quantor is 'exists' and add it as a conjunction for formulas with quantor 'forall'  */
first_step_qe(Term, NewFormula) :-
    split_term(Term, SplittedTerm),
    flatten(SplittedTerm, FlattenedTerm),
    include(is_quantifier_formula,FlattenedTerm, AllQuantFormulas),
    helper_add_excl_quantifier(AllQuantFormulas, Res),
    maplist(helper_resolve_inner, Res, ResolvQuantForms),
    replace_rec(Term, AllQuantFormulas, ResolvQuantForms, NewFormula).

/* Helper function that replaces Subterms with new Subterms*/
replace_rec(NewForm, [],_, NewForm).
replace_rec(Formula, [FirstInner|RestInner], [FirstReplInner|RestReplInner], ResNewForm) :-
    replace(FirstInner, FirstReplInner, Formula, NewForm),
    replace_rec(NewForm, RestInner, RestReplInner, ResNewForm).

/* Helper function which adds exclusive quantifiers to all inner quantifier formulas */
helper_resolve_inner(Formula, Formula) :-
    getAllQuantifierFormulas(Formula, Inners),
    Inners = [].
helper_resolve_inner(Formula, NewFormula1) :-
    getAllQuantifierFormulas(Formula, Inners),
    Inners \= [],
    helper_add_excl_quantifier(Inners, ResolvedInners),
    replace_rec(Formula, Inners, ResolvedInners, NewFormula),
    helper_resolve_inner(NewFormula, NewFormula1).

/* Helper function which adds exclusive quantifiers to all quantifier formulas */
helper_add_excl_quantifier([],[]).
helper_add_excl_quantifier([FirstQuantForm|RestQuantForm], HelperExclQuantForm) :-
    getInnerFormula(FirstQuantForm, InnerForm),
    extract_bound_vars(FirstQuantForm, Boundvars),
    freevars(FirstQuantForm, Freevars),
    helper_qe_repl_quant(InnerForm, Boundvars, Freevars, NewInnerForms),
    helper_dis_or_con(FirstQuantForm, InnerForm, Boundvars, Freevars, NewInnerForms, NewQuantForm),
    append([NewQuantForm], Out, HelperExclQuantForm),
    helper_add_excl_quantifier(RestQuantForm, Out).

/* Helper function which replaces boundvars with freevars */
    helper_qe_repl_quant(InnerFormula, Boundvars, Freevars, Res) :-
    length(Freevars, LenFreevars),
    length(Boundvars, LenBoundvars),
    copy_list(Boundvars, LenFreevars, EnoughBoundvars),
    LenEnoughFormula is LenFreevars * LenBoundvars,
    copy_list([InnerFormula], LenEnoughFormula, EnoughFormulas),
    copy_list(Freevars, LenBoundvars, EnoughFreevars),
    seperate_elems_in_a_list(EnoughBoundvars, Sep1),
    seperate_elems_in_a_list(EnoughFreevars, Sep2),
    maplist(replace_rec, EnoughFormulas, Sep1, Sep2, Res).


/* Helper function which adds the right operator depending on the quantifier */
helper_dis_or_con(QuantForm, Form,Boundvars, Freevars, [], exists(Boundvars, Freevars,Form)) :-
    QuantForm = exists(_,_).
helper_dis_or_con(QuantForm, Form,Boundvars, Freevars, [], forall(Boundvars, Freevars,Form)) :-
    QuantForm = forall(_,_).
helper_dis_or_con(QuantForm, InnerForm, Boundvars,Freevars, [FirstForm|RestForm], DisOrCon) :-
    QuantForm = exists(_,_),
    helper_dis_or_con(QuantForm, InnerForm or FirstForm,Boundvars,Freevars, RestForm, DisOrCon).
helper_dis_or_con(QuantForm, InnerForm, Boundvars,Freevars,[FirstForm|RestForm], DisOrCon) :-
    QuantForm = forall(_,_),
    helper_dis_or_con(QuantForm, InnerForm and FirstForm, Boundvars,Freevars,RestForm, DisOrCon).


/* Build DNF (Disjunctive Normal Form), taken from pseudocode of the Bachelor thesis named Asymptotic Quantifier Elimination
 *  by Marian Lingsch Rosenfeld  p.5 */
build_negation_normal_form(Phi, not(P) and not(Q)) :-
    Phi == not(P or Q).
build_negation_normal_form(Phi, not(P) or not(Q)) :-
    Phi == not(P and Q).
build_negation_normal_form(Phi, P) :-
    Phi == not(not(P)).
build_negation_normal_form(Phi, Phi) :-
    Phi \= not(P or Q),
    Phi \= not(P and Q),
	Phi \= not(not(P)).

build_dnf_rec(Phi or Psi, Phi_r or Psi_r) :-
    build_dnf_rec(Phi, Phi_r),
    build_dnf_rec(Psi, Psi_r),!.
build_dnf_rec(Phi and (Psi or Chi), (Phi_r and Psi_r) or (Phi_r and Chi_r)) :-
    build_dnf_rec(Phi, Phi_r),
    build_dnf_rec(Psi, Psi_r),
    build_dnf_rec(Chi,Chi_r),!.
build_dnf_rec((Psi or Chi) and Phi, (Psi_r and Phi_r) or (Chi_r and Phi_r)) :-
    build_dnf_rec(Phi, Phi_r),
    build_dnf_rec(Psi, Psi_r),
    build_dnf_rec(Chi,Chi_r),!.
build_dnf_rec(Phi and Psi,(Phi_r and Psi_r)) :-
    build_dnf_rec(Phi, Phi_r),
    build_dnf_rec(Psi, Psi_r),!.
build_dnf_rec(forall(Boundvars,Freevars,Phi), forall(Boundvars,Freevars,Phi_r)) :-
    build_dnf_rec(Phi, Phi_r),!.
build_dnf_rec(exists(Boundvars,Freevars,Phi), exists(Boundvars,Freevars,Phi_r)) :-
    build_dnf_rec(Phi, Phi_r),!.
build_dnf_rec(Phi, Phi) :-
    \+sub_term(or, Phi),
    \+sub_term(and, Phi),
    \+sub_term(forall, Phi),
    \+sub_term(exists, Phi).

while_dnf(Phi, NewPsi_r) :-
    build_negation_normal_form(Phi,Psi),
    build_dnf_rec(Psi, NewPsi),
    Psi \= NewPsi,
    while_dnf(NewPsi, NewPsi_r).
while_dnf(Phi, NewPsi) :-
    build_negation_normal_form(Phi,Psi),
    build_dnf_rec(Psi, NewPsi),
    Psi == NewPsi.

build_dnf(Phi, NewPsi) :-
    while_dnf(Phi, NewPsi).

split_term_at_or(Phi or Psi, [Phi_r, Psi_r]) :-
   split_term_at_or(Phi, Phi_r),
    split_term_at_or(Psi, Psi_r),!.
split_term_at_or(Phi,[Phi]) :-
    \+sub_term(or, Phi),
    \+sub_term(and, Phi).

is_excl_quant_form(forall(_,_,_)).
is_excl_quant_form(exists(_,_,_)).


getAllExclQuantifierFormulas(Formula, AllExclQuantFormulas) :-
    findall(Value, sub_term(Value, Formula), SubTermList),
    include(is_excl_quant_form,SubTermList, AllExclQuantFormulas).

getAllExclQuantifierBoundvars(forall(Boundvars,_,_), Boundvars).
getAllExclQuantifierBoundvars(exists(Boundvars,_,_), Boundvars).


getAllExclQuantifierInnerPart(forall(_,_,InnerPart), InnerPart).
getAllExclQuantifierInnerPart(exists(_,_,InnerPart), InnerPart).


list_to_conj([], []).
list_to_conj(Parts, [Conj]) :-
    Parts \= [],
    maplist(term_to_atom,Parts, AtomicTerm),
    atomic_list_concat(AtomicTerm, ' and ', AtomicConjunction),
    term_to_atom(Conj, AtomicConjunction).


list_to_disj([], []).
list_to_disj(Parts, [Disj]) :-
    Parts \= [],
    maplist(term_to_atom,Parts, AtomicTerm),
    atomic_list_concat(AtomicTerm, ' or ', AtomicConjunction),
    term_to_atom(Disj, AtomicConjunction).


make_nested_list([],[]).
make_nested_list([First|Rest],Res) :-
    append([[First]], Out, Res),
    make_nested_list(Rest, Out).

include_literals(ConjList, SplitConj) :-
    flatten1(ConjList, FlatConj),
    findall(Value, sub_term(Value, FlatConj), SubTermList),
    include(getLiteral,SubTermList, SplitConj).

/* Checks if a Literal is a Fep */
is_free_elem_part([],FreeElems,[FreeElems]).
is_free_elem_part([FirstBoundvar|RestBoundvar], Literals, AllFreeElems) :-
   exclude(sub_term(FirstBoundvar), Literals, FreeElems),
   is_free_elem_part(RestBoundvar, FreeElems, AllFreeElems).

/* Helper predicate which seperates the Non-fep and Fep */
helper_split_up_fep([],_, []).
helper_split_up_fep([FirstPart|RestPart],SortedBoundvars,FinalNewConjs) :-
    length(FirstPart, LenConjunctions),
    copy_list([SortedBoundvars], LenConjunctions, EnoughBoundvars),
    make_nested_list(FirstPart, NestedList),
    maplist(include_literals, NestedList, Literals),
    maplist(flatten, Literals, FlatLiterals),
	maplist(is_free_elem_part,EnoughBoundvars,FlatLiterals, FreeElems),
    maplist(flatten, FreeElems, FlatFreeElems),
    maplist(subtract, FlatLiterals, FlatFreeElems, NonFreeElems),
    maplist(list_to_conj, NonFreeElems, NonFreeElemsConj),
    maplist(list_to_conj, FlatFreeElems, FlatFreeElemsConj),
    maplist(helper_add, NonFreeElemsConj, FlatFreeElemsConj, Res),
    maplist(list_to_conj, Res, NewConjs),
    append(NewConjs, Out, FinalNewConjs),
    helper_split_up_fep(RestPart, SortedBoundvars, Out).

/* Helper predicate that joins the list of Non-Fep and Fep together into one list */
helper_add([], [], []).
helper_add(Conj,[],Conj) :-
    Conj \= [].
helper_add([],Conj,Conj) :-
    Conj \= [].
helper_add([FirstElem|RestElem], [OtherElem|RestOtherElem], Result) :-
    [FirstElem|RestElem] \= [],
    [OtherElem|RestOtherElem] \= [],
    NewList = [FirstElem, OtherElem],
    append(NewList, Out, Result),
    helper_add(RestElem, RestOtherElem, Out).

/* Each term with a quantifier has in its conjunction on one side fep and on the other side non-fep */
split_up_free_elems_term([], []).
split_up_free_elems_term([FirstTerm|RestTerm], NewForms) :-
    getAllExclQuantifierFormulas(FirstTerm, ExclQuantFormula),
    maplist(getAllExclQuantifierBoundvars,ExclQuantFormula, Boundvars),
    flatten(Boundvars, FlattenedBoundvars),
    sort(FlattenedBoundvars, SortedBoundvars),
    maplist(getAllExclQuantifierInnerPart, ExclQuantFormula, InnerParts),
    maplist(split_term, InnerParts, SplitConjs),
    maplist(flatten, SplitConjs, Flatten),
    maplist(exclude(is_excl_quant_form), Flatten, Literals),
    maplist(list_to_conj, Literals, ConjLiterals),
    maplist(flatten, ConjLiterals, FlatTerms),
    flatten(FlatTerms, MoreFlattenedTerms),
    helper_split_up_fep(FlatTerms, SortedBoundvars, NewConjs),
    flatten(NewConjs, FlattenedNewConjs),
    replace_rec(FirstTerm, MoreFlattenedTerms,FlattenedNewConjs, NewForm),
    append([NewForm], Out, NewForms),
    split_up_free_elems_term(RestTerm, Out).


/* Splits term at 'or' and  puts with the help of split_up_free_elems fep and non-fep at one side
 * and puts them together as disjunction again */
split_up_free_elems(Term, FinalDisjTerm) :-
    split_term_at_or(Term, SplittedTerm),
    flatten(SplittedTerm, Flattened),
    split_up_free_elems_term(Flattened, Res),
    list_to_disj(Res, FinalDisj),
    flatten1(FinalDisj, FinalDisjTerm).


/* Helper predicate that splits the inner term of a quantifier terms at 'or' */
helper_inner_part1(exists(BV,FV,InnerPart), exists(BV,FV,RelvSplitConj)) :-
    split_term_at_or(InnerPart,Ors),
    flatten(Ors, Conjs),
    maplist(split_term, Conjs, SplitConj),
    maplist(flatten, SplitConj, FlatConjs),
    maplist(exclude(is_excl_quant_form), FlatConjs, RelvSplitConj).
helper_inner_part1(forall(BV,FV,InnerPart), forall(BV,FV,RelvSplitConj)) :-
    split_term_at_or(InnerPart,Ors),
    flatten(Ors, Conjs),
    maplist(split_term, Conjs, SplitConj),
    maplist(flatten, SplitConj, FlatConjs),
    maplist(exclude(is_excl_quant_form), FlatConjs, RelvSplitConj).

/* Helper predicate that maps non-fep to true or false depending on the quantifier */
helper_map_non_fep(exists(Boundvars, _, Literals),FlatInnerPart) :-
    maplist(list_to_conj,Literals, InnerPart),
    length(InnerPart, LenInnerPart),
    copy_list([Boundvars], LenInnerPart, EnoughBoundvars),
    maplist(is_free_elem_part, EnoughBoundvars, Literals, FreeElems),
    maplist(flatten, FreeElems, FlatFreeElems),
    maplist(subtract, Literals, FlatFreeElems, NonFreeElems),
    filter_negated_parts(NonFreeElems, NegatedNonFreeElems),
    maplist(subtract, NonFreeElems, NegatedNonFreeElems, NormalNonFreeElems),
    maplist(length, NegatedNonFreeElems, LenNegatedNonFreeElems),
    maplist(length, NormalNonFreeElems, LenNormalNonFreeElems),
    maplist(copy_list([true]), LenNormalNonFreeElems, EnoughTrue),
    maplist(copy_list([false]), LenNegatedNonFreeElems, EnoughFalse),
    maplist(replace_rec, InnerPart, NormalNonFreeElems, EnoughTrue, NewInnerPart),
    maplist(replace_rec, NewInnerPart, NegatedNonFreeElems, EnoughFalse,
            NewInnerPartNegatedMapped),
    flatten(NewInnerPartNegatedMapped,FlatNewInnerPart),
    maplist(split_term, FlatNewInnerPart, SplitInnerPart),
    flatten(SplitInnerPart, FlatInnerPart).
helper_map_non_fep(forall(Boundvars, _, Literals),FlatInnerPart) :-
    maplist(list_to_conj,Literals, InnerPart),
    length(InnerPart, LenInnerPart),
    copy_list([Boundvars], LenInnerPart, EnoughBoundvars),
    maplist(is_free_elem_part, EnoughBoundvars, Literals, FreeElems),
    maplist(flatten, FreeElems, FlatFreeElems),
    maplist(subtract, Literals, FlatFreeElems, NonFreeElems),
    filter_negated_parts(NonFreeElems, NegatedNonFreeElems),
    maplist(subtract, NonFreeElems, NegatedNonFreeElems, NormalNonFreeElems),
    maplist(length, NegatedNonFreeElems, LenNegatedNonFreeElems),
    maplist(copy_list([true]), LenNegatedNonFreeElems, EnoughTrue),
    maplist(length, NormalNonFreeElems, LenNormalNonFreeElems),
    maplist(copy_list([false]), LenNormalNonFreeElems, EnoughFalse),
    maplist(replace_rec, InnerPart, NormalNonFreeElems, EnoughFalse, NewInnerPart),
    maplist(replace_rec, NewInnerPart, NegatedNonFreeElems, EnoughTrue,
            NewInnerPartNegatedMapped),
    flatten(NewInnerPartNegatedMapped,FlatNewInnerPart),
    maplist(split_term, FlatNewInnerPart, SplitInnerPart),
    flatten(SplitInnerPart, FlatInnerPart).

/* Parts with no free-elementary parts are equivalent to true or false (depending on the quantifier) */
map_non_fep(Term, Result) :-
    split_term_at_or(Term, SplittedTerm),
    flatten(SplittedTerm, Flattened),
    getAllExclQuantifierFormulas(Flattened, ExclQuantFormula),
    maplist(getAllExclQuantifierInnerPart, ExclQuantFormula, InnerParts),
    maplist(split_term_at_or, InnerParts, SplitOrs),
    flatten(SplitOrs, FlatSplitOrs),
    maplist(split_term, FlatSplitOrs, SplitConjs),
    maplist(flatten, SplitConjs, Flatten),
    maplist(exclude(is_excl_quant_form), Flatten, Relv),
    maplist(helper_inner_part1, ExclQuantFormula, ConjLiterals),
    maplist(helper_map_non_fep, ConjLiterals, New),
    flatten(New, FlatNew),
    flatten(Relv, FlatRelv),
    term_to_atom1(Term, AtomTerm),
    maplist(term_to_atom1, FlatRelv, RelvAtoms),
    maplist(term_to_atom1, FlatNew, FlatNewAtoms),
    replace_nth_word_rec(AtomTerm, 1, RelvAtoms, FlatNewAtoms, NewTerm),
    term_to_atom(Result, NewTerm).

/* All steps of quantifier-elimination */
reduced_quant_elim(Term, ReducedTerm) :-
    first_step_qe(Term, FirstStepTerm),
    build_dnf(FirstStepTerm, DnfTerm),
    split_up_free_elems(DnfTerm, SplitFepTerm),
    map_non_fep(SplitFepTerm, MappedTerm),
    reduced_form(MappedTerm, ReducedTerm),!.

/* Convert the result of the isfr back to a logic program */
convert_to_lp(Pred,Freevars,true,[Clause]) :-
    Clause = Pred-Freevars-[].
convert_to_lp(_,_,false,[]).
convert_to_lp(Pred,Freevars,Formula, LP) :-
    Formula \= true,
    Formula \= false,
    Head = Pred-Freevars,
    split_term_at_or(Formula, SplittedTerm),
    flatten(SplittedTerm, FlatSplittedTerm),
    maplist(split_term, FlatSplittedTerm, SplitConjs),
    length(SplitConjs, LenConjs),
    copy_list([Head], LenConjs, EnoughHeads),
    maplist(flatten, SplitConjs,FlatSplitConjs),
    maplist(put_together, EnoughHeads, FlatSplitConjs, LP).


/* Checks if a list contains a term and the negation of the term */
notsath(List) :- member(X,List), member(not(X), List).
notsat(List) :- member(InnerList,List) -> notsath(InnerList).

/* helper predicate to build the negation of the term */
addnot(Part, not(Part)) :-
    \+is_list(Part).
addnot([],[]).
addnot([FirstPart|RestPart], NotList) :-
    append([not(FirstPart)], Out, NotList),
    addnot(RestPart,Out).

/* helper predicate to filter for negated parts */
getNegatedParts(not(_)).

filter_negated_parts([],[]).
filter_negated_parts([First|Rest], Res) :-
    include(getNegatedParts, First, FirstRes),
    append([FirstRes], Out, Res),
    filter_negated_parts(Rest, Out).

/* A = A or B <=> B => A <=> not(B) or A <=> B and not(A) */
transform_term(A, B, B and FlatNotConj) :-
    split_term_at_or(A,Split),
    flatten(Split, FlatSplit),
    maplist(split_term, FlatSplit, SplitConjs),
    maplist(flatten,SplitConjs, FlatSplitConjs),
    maplist(addnot,FlatSplitConjs, NotList),
    maplist(list_to_conj,NotList,NotConj),
    flatten(NotConj, FlatList),
    list_to_disj(FlatList,DisjList),
    flatten1(DisjList, FlatNotConj),!.

/* Termination condition for the isfr */
terminate_isfr(TransfTerm) :-
    while_dnf(TransfTerm,Dnf),
    split_term_at_or(Dnf,SplitTerm),
	flatten(SplitTerm, FlatSplitTerm),
	maplist(split_term, FlatSplitTerm, SplitConjs),
	maplist(flatten, SplitConjs, FlatSplitConjs),
    notsat(FlatSplitConjs),!.

stratify(Program,Predicates,Strata) :-
    length(Strata,N),
    Strata ins 0..N,
    stratification(Program,Predicates,Strata),
    once(labeling([],Strata)).

stratification([],_,_).
stratification([Clause|Program],Predicates,Strata) :-
    safe_clause(Clause,Predicates,Strata),
    stratification(Program,Predicates,Strata).

safe_clause(_-[],_,_).
safe_clause(Head-[Body1|Bodyrest],Predicates,Strata) :-
    Body1 = not(Atom),
    Head = Headpred-_,
    Atom = Bodypred-_,
%%    select(Headpred,Predicates,H,Strata),
    nth1(N_H,Predicates,Headpred),
    nth1(N_H,Strata,H),
%%    select(Bodypred,Predicates,B,Strata),
    nth1(N_B,Predicates,Bodypred),
    nth1(N_B,Strata,B),
    B #< H,
    safe_clause(Head-Bodyrest,Predicates,Strata).
safe_clause(Head-[Body1|Bodyrest],Predicates,Strata) :-
    Body1 \= not(_),
    Head  = Headpred-_,
    Body1 = Bodypred-_,
%%    select(Headpred,Predicates,H,Strata),
    nth1(N_H,Predicates,Headpred),
    nth1(N_H,Strata,H),
%%    select(Bodypred,Predicates,B,Strata),
    nth1(N_B,Predicates,Bodypred),
    nth1(N_B,Strata,B),
    B #=< H,
    safe_clause(Head-Bodyrest,Predicates,Strata).

getElemWithGivenIndex(_,[],[]).
getElemWithGivenIndex(List,[FirstInd|RestInd],Sublist) :-
    nth1(FirstInd,List,Elem),
    append([Elem], Out, Sublist),
    getElemWithGivenIndex(List, RestInd,Out).

/* Adds the lfp-constructor for a a predicate*/
compute_lfp(Pred,slfp(Preds, Slfp,FreeVars),Lfp,RelvFreeVars) :-
 nth1(Index, Preds, Pred),
 nth1(Index, FreeVars, RelvFreeVars),
 nth1(Index, Slfp, RelvForm),
 build_lfp_constructor(Pred, RelvForm, Lfp).

/* Helper predicates for computing replacers*/
compute_replacer([], _, []).
compute_replacer([FirstSub|RestSub], Repl, ReplList) :-
    \+sub_term(not(_), FirstSub),
    append([Repl], Out, ReplList),
    compute_replacer(RestSub, Repl, Out).
compute_replacer([FirstSub|RestSub], Repl, ReplList) :-
    sub_term(not(_), FirstSub),
    append([not(Repl)], Out, ReplList),
    compute_replacer(RestSub, Repl, Out).

/* Computes strata for logic programs with negation and labels each predicate with a number */
compute_strata(Program, Strata,SortedAllPreds) :-
    intentionals(Program, HeadPreds),
	bodyPreds(Program, BodyPreds),
	append(HeadPreds, BodyPreds, AllPreds),
    sort(AllPreds, SortedAllPreds),
    once(stratify(Program,SortedAllPreds,Strata)).

/* Get the right execution order for computing the lfp-formulas according to the strata */
compute_order_preds([],[],[]).
compute_order_preds(Strata, Preds, AscOrderedPreds) :-
    min_list(Strata, Min),
    findall(Index,nth1(Index,Strata,Min),RelvInds),
    getElemWithGivenIndex(Preds, RelvInds, RelvPreds),
    append(RelvPreds, Out, AscOrderedPreds),
    subtract(Preds, RelvPreds, RestPreds),
    subtract(Strata, [Min], RestStrata),
    compute_order_preds(RestStrata, RestPreds, Out).

/* Predicate which executes the replacement of predicates in a lfp-formula */
do_replacement1([LastPred],Preds, Lfps, FinalLfps) :-
    do_replacement(LastPred,Preds,Lfps,FinalLfp),
    nth1(Index, Preds,LastPred),
    nth1(Index,Lfps, LastLfp),
    select(LastLfp,Lfps,FinalLfp, FinalLfps).
do_replacement1([FirstPred|RestPred],Preds, Lfps, EndResultLfps) :-
    nth1(Index, Preds,FirstPred),
    nth1(Index,Lfps, CurrLfp),
    PlusOne is Index + 1,
    nth1(PlusOne,Lfps, NextLfp),
    findall(Value, sub_term(Value, [NextLfp]), SuLi),
    include(getLiteral, SuLi, Literals),
    include(checkPredLiteral(FirstPred), Literals, RelvLiterals),
    compute_replacer(RelvLiterals, CurrLfp, Replacers),
    maplist(variables_in_literal, RelvLiterals, RelvVars),
    maplist(reduced_form,Replacers, ReducedReplacers),
    maplist(freevars, ReducedReplacers, ReplVars),
    maplist(reduced_form, Replacers, RedReplacers),
    flatten(ReplVars,FlatReplVars),
    flatten(RelvVars,FlatRelvVars),
    sort(FlatReplVars, SortedFlatReplVars),
    sort(FlatRelvVars, SortedRelvVars),
    length(SortedFlatReplVars, LenReplVars),
    length(SortedRelvVars, LenRelvVars),
    LenReplVars == LenRelvVars,
    maplist(replace_rec, RedReplacers, ReplVars, RelvVars, NewReplacers),
    replace_rec(NextLfp, RelvLiterals, NewReplacers, ReplForm),
    select(NextLfp, Lfps, ReplForm, NewLfps),
    do_replacement1(RestPred,Preds,NewLfps, EndResultLfps).
do_replacement1([FirstPred|RestPred],Preds, Lfps, EndResultLfps) :-
    nth1(Index, Preds,FirstPred),
    nth1(Index,Lfps, CurrLfp),
    PlusOne is Index + 1,
    nth1(PlusOne,Lfps, NextLfp),
    findall(Value, sub_term(Value, [NextLfp]), SuLi),
    include(getLiteral, SuLi, Literals),
    include(checkPredLiteral(FirstPred), Literals, RelvLiterals),
    compute_replacer(RelvLiterals, CurrLfp, Replacers),
    maplist(variables_in_literal, RelvLiterals, RelvVars),
    maplist(reduced_form, Replacers, RedReplacers),
    maplist(freevars, RedReplacers, ReplVars),
    flatten(ReplVars,FlatReplVars),
    flatten(RelvVars,FlatRelvVars),
    sort(FlatReplVars, SortedFlatReplVars),
    sort(FlatRelvVars, SortedRelvVars),
    length(SortedFlatReplVars, LenReplVars),
    length(SortedRelvVars, LenRelvVars),
    LenReplVars \= LenRelvVars,
    replace_rec(NextLfp, [], [], ReplForm),
    select(NextLfp, Lfps, ReplForm, NewLfps),
    do_replacement1(RestPred,Preds,NewLfps, EndResultLfps).


do_replacement(Pred,AscOrdPreds, Lfps, FinalLfp) :-
    nth1(Index,AscOrdPreds,Pred),
    nth1(Index,Lfps, RelvLfp),
    findall(Value, sub_term(Value, RelvLfp), SuLi),
    include(getLiteral, SuLi, Literals),
    sort(Literals, SortedLiterals),
    subtract(AscOrdPreds, [Pred], RemPreds),
    look_for_repl_literals(RemPreds, AscOrdPreds,Lfps, SortedLiterals, RelvLfp, FinalLfp).

variables_of_formula(Form, Vars) :-
    getBoundVarsOfFormula([Form],BV),
    freevars(Form,FV),
    union(BV,FV,Vars).

/* Looks in a lfp-formula if there are predicates which can be replaced and computes the replacers */
look_for_repl_literals([], _,_, _, RelvForm,RelvForm).
look_for_repl_literals([FirstRemPred|RestRemPred], Preds,Lfps, SortedLiterals, RelvForm, NewForm) :-
    include(checkPredLiteral(FirstRemPred), SortedLiterals, RelvLiterals),
    nth1(Index,Preds,FirstRemPred),
    nth1(Index,Lfps, Repl),
    compute_replacer(RelvLiterals, Repl, Replacers),
    maplist(variables_in_literal, RelvLiterals, RelvVars),
    maplist(freevars, Replacers, ReplVars),
    maplist(reduced_form, Replacers, RedReplacers),
    maplist(replace_rec, RedReplacers, ReplVars, RelvVars, NewReplacers),
    replace_rec(RelvForm, RelvLiterals, NewReplacers, ReplForm),
    look_for_repl_literals(RestRemPred, Preds,Lfps, SortedLiterals, ReplForm, NewForm).

/* Adds recursively to all formulas of a logic program the lfp-constructor if necessary */
compute_rec_lfp(_,[],_,[]).
compute_rec_lfp(Program, [FirstPred|RestPred],slfp(Preds,Slfps,FreeVars),AllLfps) :-
    intentionals(Program, Int),
    \+member(FirstPred, Int),
    compute_rec_lfp(Program,RestPred,slfp(Preds,Slfps,FreeVars),AllLfps).
compute_rec_lfp(Program, [FirstPred|RestPred],slfp(Preds,Slfps,FreeVars),AllLfps) :-
    intentionals(Program, Int),
    member(FirstPred, Int),
    compute_lfp(FirstPred, slfp(Preds,Slfps,FreeVars),FirstLfp, _),
    append([FirstLfp], Out, AllLfps),
    compute_rec_lfp(Program, RestPred,slfp(Preds,Slfps,FreeVars), Out).

/* Computes the Lfp-formula of a logic program which contains negative predicates */
compute_for_negation(Program, Pred,SubVars,RelvFreeVars,FinalLfp) :-
    datalog_to_formula(Program-Pred,SubVars,slfp(Preds,Slfps,FreeVars)),
    compute_strata(Program, Strata, OrderPreds),
    compute_order_preds(Strata, OrderPreds, AscOrdPreds),
    reverse(Preds,RevPreds),
    intersection(RevPreds, AscOrdPreds, OrderedPreds),
    compute_rec_lfp(Program, OrderedPreds,slfp(Preds,Slfps,FreeVars), Lfps),
    intentionals(Program, Intentionals),
    intersection(OrderedPreds, Intentionals, IntersecPreds),
    do_replacement1(IntersecPreds,IntersecPreds, Lfps, FinalLfps),
    nth1(Index, IntersecPreds,Pred),
    nth1(Index,FinalLfps, FinalLfp),
    nth1(Index1, Preds, Pred),
    nth1(Index1, FreeVars, RelvFreeVars).

/* Computes the Lfp-formula of a logic program with only positive predicates */
compute_for_pos(Program, Pred,SubVars,RelvFreeVars,FinalLfp) :-
    datalog_to_formula(Program-Pred,SubVars, slfp(Preds,Slfps,FreeVars)),
    reverse(Preds, RevPreds),
	compute_rec_lfp(Program, RevPreds,slfp(Preds,Slfps,FreeVars), Lfps),
    do_replacement1(RevPreds,RevPreds, Lfps, FinalLfps),
    nth1(Index, RevPreds,Pred),
    nth1(Index,FinalLfps, FinalLfp),
	nth1(Index1, Preds, Pred),
    nth1(Index1, FreeVars, RelvFreeVars).

/* A logic program is asymptotically transformed into a det. logic program */
compute_lp_form(Program,Pred,SortedLogProg) :-
    compute_lp_form(Program,Pred,[a,b,c,d,e,f,g,h],SortedLogProg).

compute_lp_form(Program, Pred, SubVars,SortedLogProg) :-
    contains_term(not(_), Program),
    compute_for_negation(Program, Pred,SubVars,Freevars, Lfp),
    compute_alpha(Lfp,AllLfps, _,AlphaConstr),
	replace_lfps(Lfp, AlphaConstr, LfpResult),
	get_iter_numbers(AlphaConstr, Iterations),
    reverse(AllLfps,RevAllLfps),
    reverse(Iterations, RevIterations),
    resolve_isfr(LfpResult,RevAllLfps,RevIterations,RevAllLfps,ReducedInnerForm),
    flatten1(ReducedInnerForm, FlatReducedInnerForm),
	convert_to_lp(Pred,Freevars, FlatReducedInnerForm, LogProg),
    sort(LogProg, SortedLogProg),!.
compute_lp_form(Program, Pred,SubVars,SortedLogProg) :-
    \+contains_term(not(_), Program),
    compute_for_pos(Program, Pred, SubVars,Freevars,Lfp),
    compute_alpha(Lfp, AllLfps, _,AlphaConstr),
	replace_lfps(Lfp, AlphaConstr, LfpResult),
	get_iter_numbers(AlphaConstr, Iterations),
    reverse(AllLfps,RevAllLfps),
    reverse(Iterations, RevIterations),
    resolve_isfr(LfpResult,RevAllLfps,RevIterations,RevAllLfps,ReducedInnerForm),
    flatten1(ReducedInnerForm, FlatReducedInnerForm),
	convert_to_lp(Pred,Freevars, FlatReducedInnerForm, LogProg),
    sort(LogProg, SortedLogProg),!.

compute_lfp_form(Lfp, ReducedInnerForm) :-
    compute_alpha(Lfp, AllLfps, _,AlphaConstr),
	replace_lfps(Lfp, AlphaConstr, LfpResult),
	get_iter_numbers(AlphaConstr, Iterations),
    reverse(AllLfps,RevAllLfps),
    reverse(Iterations, RevIterations),
    resolve_isfr(LfpResult,RevAllLfps,RevIterations,RevAllLfps,ReducedInnerForm),
    !.

compute_lp_lfp(Program,Pred,Lfp) :-
    compute_lp_lfp(Program,Pred,[a,b,c,d,e,f,g,h],Lfp).

compute_lp_lfp(Program,Pred,SubVars,Lfp) :-
    contains_term(not(_), Program),
    compute_for_negation(Program, Pred,SubVars,_, Lfp).
compute_lp_lfp(Program,Pred,SubVars,Lfp) :-
    \+contains_term(not(_), Program),
    compute_for_pos(Program, Pred, SubVars,_,Lfp).


get_inner_pred(lfp(Pred,_),Pred).
get_form(lfp(_,Form),Form).
get_form(Form,Form) :-
    Form \= lfp(_,_).

/* Applies the iteration stage formation rule to a formula.
 * This also works on nested formulas */
resolve_isfr(_,[Formula],[FirstIter],[Formula],[ReducedForm]) :-
    Formula = lfp(LfpPred,Form),
    isfr1(FirstIter,0,Form,[LfpPred],false,ReducedForm).
resolve_isfr(Form,[], [],_,[ReducedForm]) :-
    Form \= lfp(_,_),
    reduced_quant_elim(Form, ReducedForm).
resolve_isfr(_,[FirstForm|_], [FirstIter|RestIter],Formulas,Res) :-
    get_inner_pred(FirstForm,Pred),
    get_form(FirstForm,Form),
    isfr1(FirstIter,0,Form,[Pred],false,ReducedForm),
    length(Formulas, LenFormulas),
    copy_list([ReducedForm], LenFormulas, EnoughReducedForm),
    copy_list([FirstForm], LenFormulas, EnoughFirstForm),
    maplist(replace,EnoughFirstForm,EnoughReducedForm,Formulas, NewFormulas),
    length(NewFormulas, LenNewFormulas),
    LenNewFormulas > 1,
    removehead(NewFormulas, WHReducedNewFormulas),
    resolve_isfr(_,WHReducedNewFormulas, RestIter,WHReducedNewFormulas,Res).
resolve_isfr(_,[FirstForm|_], [FirstIter|RestIter],Formulas,Res) :-
    get_inner_pred(FirstForm,Pred),
    get_form(FirstForm,Form),
    isfr1(FirstIter,0,Form,[Pred],false,ReducedForm),
    length(Formulas, LenFormulas),
    copy_list([ReducedForm], LenFormulas, EnoughReducedForm),
    copy_list([FirstForm], LenFormulas, EnoughFirstForm),
    maplist(replace,EnoughFirstForm,EnoughReducedForm,Formulas, NewFormulas),
    length(NewFormulas, LenNewFormulas),
    LenNewFormulas == 1,
    resolve_isfr(_,NewFormulas, RestIter,NewFormulas,Res).

unique([]).
unique([_,[]]).
unique([H|T]):-not(member(H,T)),unique(T).

getIndexOfDupl([],_,[]).
getIndexOfDupl([FirstDupl|RestDupl], Vars, Inds) :-
    findall(Index,nth0(Index,Vars,FirstDupl),RelvInds),
    append([RelvInds], Out, Inds),
    getIndexOfDupl(RestDupl, Vars, Out).

getIndexOfDupl1([],_,[]).
getIndexOfDupl1([FirstDupl|RestDupl], Vars, Inds) :-
    findall(Index,nth1(Index,Vars,FirstDupl),RelvInds),
    append([RelvInds], Out, Inds),
    getIndexOfDupl1(RestDupl, Vars, Out).


get_dupl_replacers([], [], []).
get_dupl_replacers([FirstDupl|RestDupl], [FirstIndList|RestIndList], DuplRepl) :-
    length(FirstIndList, Len),
    copy_list([FirstDupl], Len, EnoughFirstDupl),
    range(OrdLi, 1, Len),
    maplist(atom_concat, EnoughFirstDupl,OrdLi, NewRepl),
    append([NewRepl], Out, DuplRepl),
    get_dupl_replacers(RestDupl, RestIndList, Out).


range([],A,B):-
    A > B.
range([A|T],A,B):-
    A =< B,
    A1 is A + 1,
    range(T,A1,B).


repl_listwise_rec(NewVars, [],[],
                  NewVars).
repl_listwise_rec(Vars, IndList,DuplReplList,
                  NewVarsList) :-
    flatten(IndList, FlatIndList),
    flatten(DuplReplList, FlatDuplReplList),
    list_nth0_item_repl_rec(Vars, FlatIndList, FlatDuplReplList, NewVarsList).

list_nth0_item_repl_rec(NewVars,[],[],NewVars).
list_nth0_item_repl_rec(Vars, [FirstInd|RestInd], [FirstDuplRepl|RestDuplRepl], NewVars) :-
    list_nth0_item_replaced(Vars, FirstInd, FirstDuplRepl, ReplVars),
    list_nth0_item_repl_rec(ReplVars, RestInd, RestDuplRepl, NewVars).

list_nth0_item_replaced([_|Xs], 0, E, [E|Xs]).
list_nth0_item_replaced([X|Xs], N, E, [X|Ys]) :-
   N #> 0,
   N #= N0+1,
   list_nth0_item_replaced(Xs, N0, E, Ys).


helper_create_pred(_, [], []).
helper_create_pred(Elem, [X|Xs], Preds) :-
    Pred = same-[Elem,X],
    append([Pred], Out, Preds),
    helper_create_pred(Elem,Xs,Out).

create_util_pred_same1(_,[], _ ,[]).
create_util_pred_same1(Vars,[FirstDupl|RestDupl], NewVars ,FinalSames) :-
  findall(Index,nth1(Index,Vars,FirstDupl),RelvInds),
  getElemWithGivenIndex(NewVars,RelvInds, BeSame),
  helper_create_pred(FirstDupl,BeSame, Sames),
  delete(Sames,same-[X,X],NewSames),
  append(NewSames, Out, FinalSames),
  create_util_pred_same1(Vars,RestDupl, NewVars, Out).

duplicates([],[]).
duplicates([X|Xs], Dupl) :-
    member(X, Xs),
    append([X],Out,Dupl),
    duplicates(Xs, Out).
duplicates([X|Xs], Dupl) :-
    \+member(X, Xs),
    duplicates(Xs, Dupl).


removehead([_|Rest], Rest).
removetail([], []).
removetail([X|_], [X]).






































