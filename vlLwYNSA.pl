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

/* This code assumes that all clauses have the form Qx_Q :- Gamma_1, ..., Gamma_l as discussed on the
 * bottom of p. 242 of Ebbinghaus and Flum's book. 
 * Some preprocessing will have to be added to get there. 
 * Also, currently all literals are assumed to be positive. */

/* A clause is represented as a pair Head-Body, where Body is a list of literals.
 * A literal is represented as a pair of a predicate symbol and a list of terms (statt variables) 
 * A Datalog formula is represented as a pair (Pi-P)-Variables, where Pi is a list of clauses, P a predicate.
 * Subvars is nested list of variables used to substitute variables when needed
 * An slfp formula is represented as slfp(list of predicates, list of formulas,Variables)*/

/* datalog_to_formula(Datalog formula, equivalent slfp formula) */
 datalog_to_formula(Datalog, Subvars, slfp(Preds,ReducedPhis,FreeVars)) :-
  Datalog = Program,
  Program = Pi-P,
  getHeadPred(Pi, HeadPreds),
  %substitution of variables  
  do_substitution(Pi, HeadPreds, Subvars, NewPi),
  include(is_clause_with_const, NewPi, ConstClauses),
  intensionals(ConstClauses, ConstHeadpreds),
  %substitution of constants
  subst_const(NewPi, ConstHeadpreds, ConstClauses, FinalConstClauses),
  subtract(NewPi, ConstClauses, NormalClauses),
  append(FinalConstClauses, NormalClauses, Endresult),
  intensionals(Pi,Ipreds),
  ord_subtract(Ipreds,[P],Ipreds_aux),
  Preds = [P|Ipreds_aux],
  getAllHeads(Endresult, AllHeads),
  sort(AllHeads, SortedHeads),
  maplist(variables_in_literal, SortedHeads, FreeVars),
  maplist(program_to_formula(Endresult),Preds,Phis),
  maplist(reduced_form, Phis, ReducedPhis).
  %extract relvant free  s of the formulas
  %sub_freevars_in_formula(Preds, ReducedPhis, SubFormula),
  %maplist(freevars, ReducedPhis, RelvFreeVars).
 
    

/* program_to_formula1(Predicate Q,Clauses,phi_Q) */
program_to_formula1(_,[],false).
program_to_formula1(Q,[Head-Body|Clauses],F or Fs) :-
    Head = Q-_,
    clause_to_formula(Head-Body,F), 
    program_to_formula1(Q,Clauses, Fs).
program_to_formula1(Q,[Head-_|Clauses],F) :-
    Head \= Q-_,
    program_to_formula1(Q,Clauses, F).

/* program_to_formula(Clauses,Predicate Q,phi_Q) */
program_to_formula(Program,Q,Phi) :-
    program_to_formula1(Q,Program,Phi).

/* conjoin_body(Body,Conjunct of literals) */
conjoin_body([],[]).
conjoin_body(Parts,Conj and true) :-
    Parts \= [],
    maplist(term_to_atom,Parts, AtomicTerm),
    atomic_list_concat(AtomicTerm, ' and ', AtomicConjunction),
    term_to_atom(Conj, AtomicConjunction).

/* clause_to_formula(Clause, Disjunct of phi_Headpredicate corresponding to Clause) */
clause_to_formula(Head-Body,Psi) :-
    include(atom, Body, AtomsInBody),
    AtomsInBody == [],
    variables_free_in_body(Head-Body,Freevars),
    clause_to_formula_aux(Head-Body,Freevars,Psi).

/* clause_to_formula(Clause, the constant of phi_Headpredicate corresponding to clause) */
clause_to_formula(Head-Body,Psi) :-
    include(atom, Body, AtomsInBody),
    AtomsInBody \= [],
    clause_to_formula_aux(Head-Body,[],Psi).

clause_to_formula_aux(_-Body,Freevars,exists(Freevars,Psi)) :-
    conjoin_body(Body,Psi).

    
/* variables_in_body(Clause, variables in the clause) */
variables_in_body(Body,Vars) :-
    maplist(extract_inner_literal, Body, PosBody),
    pairs_values(PosBody, Varss),
    append(Varss,Varsdupl),
    sort(Varsdupl,VarsAndConst),
    exclude(is_const,VarsAndConst, Vars).

variables_in_literal(_-VarsAndConst,Vars) :-
    VarsAndConst \= not(_),
    exclude(is_const,VarsAndConst, Vars).
variables_in_literal(not(X),Vars) :-
    variables_in_literal(X,Vars).

const_in_literal(_-VarsAndConst,Const) :-
    include(is_const,VarsAndConst, Const).


variables_free_in_body(Head-Body,Vars) :- 
    variables_in_literal(Head,Headvars1),
    variables_in_body(Body,Bodyvars1),
    sort(Headvars1, Headvars),
    sort(Bodyvars1, Bodyvars),
    ord_subtract(Bodyvars,Headvars,Vars),
    exclude(is_const, Vars, Vars).

extract_inner_literal(not(X), X).
extract_inner_literal(X,X) :-
    X \= not(_).

/* intensionals(Clauses, heads occuring in a clause) */
intensionals(Clauses,Headpreds) :-
    pairs_keys(Clauses,Heads),
    pairs_keys(Heads,Headpredsdupl),
    sort(Headpredsdupl,Headpreds).

/* bodyPreds(Clauses, preds occuring in a clause body but are not head of a clause) */
bodyPreds(Clauses,BodyHeads) :-
    pairs_values(Clauses, Bodies),
    flatten(Bodies, FlatBody),
    maplist(extract_inner_literal, FlatBody, BodiesDupl),
    sort(BodiesDupl, Bodypreds),
    pairs_keys(Bodypreds, BodyHeads).
    
/* We collate some trivial reduction steps to avoid overfreighting our formulas */    
:- discontiguous reducible/1.
:- discontiguous reduction_step/2.

reduction_step(Phi,Phi) :-
    getLiteral(Phi).

reduction_step(exists([],Phi),Phi_r) :-
    reduction_step(Phi, Phi_r),!.
reducible(exists([],_)).

reduction_step(forall([],Phi),Phi_r) :-
    reduction_step(Phi, Phi_r),!.
reducible(forall([],_)).

reduction_step(exists([Var],Phi),exists([Var],Phi_r)) :-
    Phi \= false,
    Phi \= true,
    reduction_step(Phi, Phi_r),!.
reduction_step(forall([Var],Phi),exists([Var],Phi_r)) :-
    Phi \= false,
    Phi \= true,
    reduction_step(Phi, Phi_r),!.

reducible(exists([_],Phi)) :-
          reducible(Phi).
reducible(forall([_],Phi)) :-
          reducible(Phi).

reduction_step(exists([_],false), false) :- !.
reduction_step(exists([_],true), true):- !.
reduction_step(forall([_],false), false):- !.
reduction_step(forall([_],true), true):- !.


reducible(exists([_],false)).
reducible(exists([_],true)).
reducible(forall([_],true)).
reducible(forall([_],false)).


reduction_step(false or Phi, Phi_r) :-
    reduction_step(Phi, Phi_r),!.
reduction_step(Phi or false, Phi_r) :-
    reduction_step(Phi, Phi_r),!.
reduction_step(false and _, false).
reduction_step(_ and false, false).
reducible(_ or false).
reducible(false or _).
reducible(_ and false).
reducible(false and _).

reduction_step(true or _, true).
reduction_step(_ or true, true).
reduction_step(true and Phi, Phi_r) :-
    reduction_step(Phi, Phi_r).
reduction_step(Phi and true, Phi_r) :-
    reduction_step(Phi, Phi_r).
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
    reducible(Phi); reducible(Psi).

reduction_step(Phi or exists([_],false), Phi).
reduction_step(exists([_],false) or Phi, Phi).
reduction_step(_ and exists([_],false), false).
reduction_step(exists([_],false) and _, false).

reduction_step(Phi and exists([_],true), Phi).
reduction_step(exists([_],true) and Phi, Phi).
reduction_step(_ or exists([_],true), true).
reduction_step(exists([_],true) or _ , true).

reduction_step(Phi or forall([_],false), Phi).
reduction_step(forall([_],false) or Phi, Phi).
reduction_step(_ and forall([_],false), false).
reduction_step(forall([_],false) and _, false).

reduction_step(Phi and forall([_],true), Phi).
reduction_step(forall([_],true) and Phi, Phi).
reduction_step(_ or forall([_],true), true).
reduction_step(forall([_],true) or _ , true).

reduction_step(not(Phi) or Phi, Phi) :- !.
reduction_step(Phi or not(Phi), Phi) :- !.
reducible(Phi or not(Phi)).
reducible(not(Phi) or Phi).

reduction_step(Phi or Psi,Phi_r or Psi_r) :-
    reduction_step(Phi,Phi_r),
    reduction_step(Psi, Psi_r).
/*reduction_step(Phi or Psi,Phi or Psi_r) :-
    reduction_step(Psi,Psi_r).*/


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


reduces_to(Phi,Phi).
reduces_to(Phi,Psi) :-
    reduces_to(Phi,Chi),
    reduction_step(Chi,Psi).
reduced_form(Phi or false, Phi_r) :-
    reduced_form(Phi, Phi_r),!.
reduced_form(false or Phi, Phi_r) :-
    reduced_form(Phi, Phi_r),!.
reduced_form(_ or true, true) :- !.
reduced_form(true or _, true) :- !.
reduced_form(_ and false, false) :- !.
reduced_form(false and _, false) :- !.

reduced_form(Phi,Psi) :-
    reduces_to(Phi,Psi),
    \+reducible(Psi), !.


/* Some list predicates */
/* replace_listwise(things to be replaced, things to replace them with, Original list, list after replacement) */
replace_listwise(_,_,[],[]).
replace_listwise(Olds,News,[O|Ldlist],[O|Ewlist]) :-
    replace_listwise(Olds,News,Ldlist,Ewlist),
    \+member(O,Olds).
replace_listwise(Olds,News,[O|Ldlist],[N|Ewlist]) :-
    replace_listwise(Olds,News,Ldlist,Ewlist),
    nth0(Index,Olds,O),
    nth0(Index,News,N).
/* corresponding_sublist(List, sublist of that list, other list, sublist of the other list with the same indices as the first sublist) */
corresponding_sublist(List,Sublist,List2,Sublist2) :-
    maplist(nth_List(List),Sublist,Indices),
    maplist(nth_List(List2),Sublist2,Indices).
nth_List(List,Elem,N) :-
    nth0(N,List,Elem).
/* substitute_clause(Variables, Terms to be substituted for variables,Original Clause, Substituted clause) */
substitute_literal(Vars,Terms,P-Oldvars,P-Newvars) :-
    P-Oldvars \= not(_),
    replace_listwise(Vars,Terms,Oldvars,Newvars).
substitute_literal(Vars,Terms,not(P-Oldvars),not(P-Newvars)) :-
    replace_listwise(Vars,Terms,Oldvars,Newvars).
substitute_clause(Vars,Terms,Head-Body,Newhead-Newbody) :-
    Head = P-Headvars,
    replace_listwise(Vars,Terms,Headvars,Newheadvars),
    Newhead = P-Newheadvars,
    maplist(substitute_literal(Vars,Terms),Body, Newbody).

substitute_heads_body(Vars,Terms,Head-Body,Newhead-NewBody) :-
    Head = P-Vars,
    Newhead = P-Terms,
    variables_in_body(Body,Bodyvars),
    intersection(Vars,Bodyvars,Intersec),
    sort(Intersec, SortedIntersec),
    getIndexOfDupl1(SortedIntersec, Vars, Inds),
    maplist(removetail, Inds, FirstInds),
    flatten(FirstInds, FlatInds),
    sort(FlatInds,SortedFlatInds),
    getElemWithGivenIndex(Terms, SortedFlatInds, RelvVars),
    replace_rec(Body,SortedIntersec,RelvVars, ReplBody),
    sort(Vars,SortedVars),
    create_util_pred_same(SortedVars, Terms, SamePreds),
    append(ReplBody,SamePreds, NewBody).


/* Some predicates to deal with variables in formulas */
/* freevars(Formula, free variables) */
freevars(true,[]).
freevars(false,[]).
freevars(_-Vars,Setvars) :-
    exclude(is_const,Vars, VarsWithOutConsts),
    sort(VarsWithOutConsts,Setvars).
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
%Hier neu schreiben
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
%LFP-FormelFall hinzugefügt
freevars(lfp(_,_),[]).
freevars(not(_-Vars), Setvars) :-
    exclude(is_const,Vars, VarsWithOutConsts),
    sort(VarsWithOutConsts,Setvars).

/* substitute_formula(Variables, Terms to be substituted for variables,Original formula, Substituted formula) */
substitute_formula(_,_,true,true).
substitute_formula(_,_,false,false).
substitute_formula(Vars,Terms,P-Oldvars,P-Newvars) :-
    replace_listwise(Vars,Terms,Oldvars,Newvars).
substitute_formula(Vars,Terms,not(P-Oldvars),not(P-Newvars)) :-
    replace_listwise(Vars,Terms,Oldvars,Newvars).
substitute_formula(Vars,Terms,Phi and Psi, Newphi and Newpsi) :-
    substitute_formula(Vars,Terms,Phi,Newphi),
    substitute_formula(Vars,Terms,Psi,Newpsi).

substitute_formula(Vars,Terms,Phi or Psi, Newphi or Newpsi) :-
    \+atom(Phi),
    \+atom(Psi),
    substitute_formula(Vars,Terms,Phi,Newphi),
    substitute_formula(Vars,Terms,Psi,Newpsi).
substitute_formula(Vars,Terms,Phi or Psi, Phi or Newpsi) :-
    atom(Phi),
    \+atom(Psi),
    substitute_formula(Vars,Terms,Psi,Newpsi).
substitute_formula(Vars,Terms,Phi or Psi, Newphi or Psi) :-
    \+atom(Phi),
    atom(Psi),
    substitute_formula(Vars,Terms,Psi,Newphi).
substitute_formula(_,_,Phi, Phi) :-
    atom(Phi).
substitute_formula(Vars,Terms,exists(Boundvars,Phi), exists(Boundvars,Newphi)) :-
    subtract(Vars,Boundvars,Freevars),
    corresponding_sublist(Vars,Freevars,Terms,Freeterms),
    substitute_formula(Freevars,Freeterms,Phi,Newphi).
substitute_formula(Vars,Terms,forall(Boundvars,Phi), forall(Boundvars,Newphi)) :-
    subtract(Vars,Boundvars,Freevars),
    corresponding_sublist(Vars,Freevars,Terms,Freeterms),
    substitute_formula(Freevars,Freeterms,Phi,Newphi).

/* Substitute formula für lfp_formeln*/
substitute_formula(Vars,Terms,lfp(Pred, Phi), lfp(Pred, Phi_r)) :-
      substitute_formula(Vars,Terms, Phi, Phi_r).

getHeadPred(Clause, NewHeadPreds) :-
    pairs_keys(Clause, Head),
    pairs_keys(Head, HeadPred),
    sort(HeadPred, NewHeadPreds).

getAllHeads(Clauses, Heads) :-
    pairs_keys(Clauses, Heads).

%Return the first element of a list
getFirst([First|_], First). 

/* Flattens a list that consists only of one element*/
flatten1([],[]).
flatten1([L],L).

%substituted clauses are replaced with first occurring head
getReplacer(Replacer1, [FirstClause|_]) :-
    getFirst([FirstClause|_], FirstClause),
    pairs_keys([FirstClause], Replacer),
    flatten1(Replacer, Replacer1).

filterClauseWithPred(Clauses, Pred, RelvClauses) :-
    include(checkPred1(Pred), Clauses, RelvClauses).

checkPred1(HeadPred, P-_-_) :-
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
    filterClauseWithPred(Clauses, FirstPred, AllRelvClauses),
    getAllHeads(AllRelvClauses, Heads),
    same(Heads),
    append(AllRelvClauses, Output, FinalNewClauses),
    do_substitution(Clauses, Rest, SubVars, Output).
do_substitution(Clauses, [FirstPred|Rest], SubVars, FinalNewClauses) :-
    %exclude(is_clause_with_const, Clauses, RelvClauses),
    filterClauseWithPred(Clauses, FirstPred, AllRelvClauses),
    getAllHeads(AllRelvClauses, Heads),
    \+same(Heads),
    getReplacer(Replacer, AllRelvClauses),
    variables_in_literal(Replacer, ReplacerVars),
    unique(ReplacerVars),
    maplist(variables_free_in_body, AllRelvClauses, FreeVars),
    length(FreeVars, LenFreeVars),
    %
    flatten1(SubVars, FlattendSubVars),
    length(FlattendSubVars, LenFlattendSubVars),
    copy_list([FirstPred], LenFlattendSubVars, EnoughPredIndices),
    maplist(atom_concat, FlattendSubVars, EnoughPredIndices, NewSubVars),
    %
    copy_list([NewSubVars], LenFreeVars, EnoughSubVars),
    maplist(substitute_clause, FreeVars, EnoughSubVars, AllRelvClauses, SubstBodyClauseVars),
    maplist(variables_in_literal, Heads, OldHeadVars),
    length(OldHeadVars, LenOldHeadVars),
    copy_list([ReplacerVars], LenOldHeadVars, NewHeadVars),
    maplist(substitute_clause, OldHeadVars, NewHeadVars, SubstBodyClauseVars, NewClauses),
    append(NewClauses, Output, FinalNewClauses),
    do_substitution(Clauses, Rest, SubVars, Output).
do_substitution(Clauses, [FirstPred|Rest], SubVars, FinalNewClauses) :-
    filterClauseWithPred(Clauses, FirstPred, AllRelvClauses),
    getAllHeads(AllRelvClauses, Heads),
    \+same(Heads),
    getReplacer(Replacer, AllRelvClauses),
    variables_in_literal(Replacer, ReplacerVars),
    %%%%%%%%%%
    \+unique(ReplacerVars),
    sort(ReplacerVars, SortedReplacerVars),
    getIndexOfDupl(SortedReplacerVars, ReplacerVars, IndList),
    get_dupl_replacers(SortedReplacerVars, IndList, DuplRepl),
    maplist(removehead, IndList, RestIndList),
    maplist(removehead, DuplRepl, RestDuplRepl),
    repl_listwise_rec(ReplacerVars, RestIndList, RestDuplRepl, NewReplVars),
    %flatten(DuplRepl, FlatDuplRepl),
    %replace_rec(ReplacerVars,ReplacerVars, FlatDuplRepl, NewReplVars),
    maplist(variables_free_in_body, AllRelvClauses, FreeVars),
    length(FreeVars, LenFreeVars),
    %
    flatten1(SubVars, FlattendSubVars),
    length(FlattendSubVars, LenFlattendSubVars),
    copy_list([FirstPred], LenFlattendSubVars, EnoughPredIndices),
    maplist(atom_concat, FlattendSubVars, EnoughPredIndices, NewSubVars),
    %
    copy_list([NewSubVars], LenFreeVars, EnoughSubVars),
    maplist(substitute_clause, FreeVars, EnoughSubVars, AllRelvClauses, SubstBodyClauseVars),
    maplist(variables_in_literal, Heads, OldHeadVars),
    length(OldHeadVars, LenOldHeadVars),
    copy_list([NewReplVars], LenOldHeadVars, NewHeadVars),
    %maplist(substitute_clause, OldHeadVars, NewHeadVars, SubstBodyClauseVars, NewClauses),
    maplist(substitute_heads_body, OldHeadVars,NewHeadVars, SubstBodyClauseVars, NewClauses),
    %append(NewClauses,SamePreds, InterResult),
    append(NewClauses, Output, FinalNewClauses),
    do_substitution(Clauses, Rest, SubVars, Output).

/* Free variables in a formula will be substituted with variable and predicate index */
sub_freevars_in_formula([],[], []).
sub_freevars_in_formula([FirstPred|Rest],[FirstFormula|RestFormula], FinalNewFormulas) :-
    freevars(FirstFormula, FreeVars),
    length(FreeVars, LenFreeVars),
    copy_list([FirstPred], LenFreeVars, EnoughPredIndices),
    maplist(atom_concat, FreeVars, EnoughPredIndices, NewFreeVars),
    substitute_formula(FreeVars, NewFreeVars, FirstFormula, NewFormula),
    append([NewFormula], Output, FinalNewFormulas),
    sub_freevars_in_formula(Rest, RestFormula, Output).

/* A filter predicate that is true if the given value is a constant*/
is_const(const(_)).

/* A predicate that substitutes constants in head with the first occurence of another predicate
 *  which has variables in their head and puts the variable in the body and the variable
 *  that the constant refers to*/
subst_const(_,[],[],[]).
subst_const(Clause, [FirstPred|Rest],FinalConstClauses,FinalNewConcats) :-
    filterClauseWithPred(Clause, FirstPred, AllRelvClauses),
    include(is_clause_with_const, AllRelvClauses, ConstClauses),
    getAllHeads(ConstClauses, ConstHeads),
    exclude(is_clause_with_const, AllRelvClauses, NormalClauses),
    getReplacer(Replacer, NormalClauses),
    variables_in_literal(Replacer, ReplacerVars),
    maplist(const_in_literal, ConstHeads, Constants),
    flatten(Constants, FlattenedConstants),
    maplist(term_to_atom, FlattenedConstants, AtomConstants),
    %FirstPred muss die richtige Anzahl haben
    length(ReplacerVars, Len),
    copy_list([FirstPred], Len, EnoughFirstPreds),
    %maplist(atom_concat, ReplacerVars, [FirstPred], ReplacerWithPred),
    maplist(atom_concat, ReplacerVars, EnoughFirstPreds, ReplacerWithPred),
    maplist(atom_concat, ReplacerWithPred, AtomConstants, Concats),
    maplist(put_together, [Replacer], [Concats], FinalConcats),
    append(FinalConcats, Output, FinalNewConcats),
    append(ConstClauses, Out, FinalConstClauses),
    subst_const(Clause, Rest, Out, Output).

/*This predicate filters out clauses with constants in the head*/
is_clause_with_const(Clause) :-
    pairs_keys([Clause], Head),
    maplist(variables_in_literal, Head, [[]]).

/* Given Head and Body, this predicate forms a literal of Head-Body */
put_together(Head, Body, Head-Body).
    

/* Replicates element in list times N */
copy_list(L, N, Copies) :-
    length(Lists, N),           % List of length N
    maplist(=(L), Lists),       % Each element of Lists is unified with L
    append(Lists, Copies).      % Lists is flattened

/* Get relevant formula of a list of formulas (relevant for slfp-formula) */
getRelevantFormula(Pred, Preds, Formulas, RelvFormula) :-
    nth0(Index, Preds, Pred),
	nth0(Index, Formulas, RelvFormula).

/* Get all subterms that should be substituted */
/* Case with operator 'or'*/
getRelevantSubterms(Pred,Preds, Phi or Psi, RelvLiteralsList) :-
    getRelevantSubterms(Pred,Preds, Phi, Phi_r),
    getRelevantSubterms(Pred,Preds, Psi, Psi_r),
    append(Phi_r, Psi_r, RelvLiteralsList), !.
/* Formula contains exists-quantor*/
getRelevantSubterms(Pred,Preds, exists([_], Phi), RelvLiteralsList) :-
    subtract(Preds, [Pred], OtherHeadPreds),
    findall(Value, sub_term(Value, Phi), SubTermList),
	include(getLiteral, SubTermList, Literals),
    getRelvLiterals(OtherHeadPreds, Literals, RelvLiteralsList),!.
/* Formula does not contain exists-quantor and has the form predicate1 and ...*/
getRelevantSubterms(Pred,Preds, Phi, RelvLiteralsList) :-
    \+atomic(Phi),
    sub_term(Sub, Phi),
    \+atomic(Sub),
    subtract(Preds, [Pred], OtherHeadPreds),
    findall(Value, sub_term(Value, Phi), SubTermList),
	include(getLiteral, SubTermList, Literals),
    getRelvLiterals(OtherHeadPreds, Literals, RelvLiteralsList).
/* Formula contains an atom*/
getRelevantSubterms(_,_, Phi, []) :-
    atomic(Phi).
    
/* Get a list of relevant literals with the help of given headpredicates */
getRelvLiterals([],_,[]).
getRelvLiterals([FirstPred|Rest], Literals, RelvLiteralsList) :-
    include(checkPredLiteral(FirstPred), Literals, RelvLiterals),
    append(RelvLiterals, Out, RelvLiteralsList),
    getRelvLiterals(Rest, Literals,Out).


/* Replaces subterms in a slfp-formula */
substitute_subterm(ToBeSubst, Replacer, ToBeSubst, Replacer).
substitute_subterm(_, _, Phi, Phi) :-
    atomic(Phi).
substitute_subterm(ToBeSubst, Replacer, Phi or Psi, Phi_r or Psi_r) :-
    substitute_subterm(ToBeSubst, Replacer, Phi, Phi_r),
    substitute_subterm(ToBeSubst, Replacer, Psi, Psi_r).
substitute_subterm(Phi, Replacer, Phi and Psi, Replacer and Psi).
substitute_subterm(ToBeSubst, Replacer, Phi and Psi, Phi and Result) :-
    ToBeSubst \= Phi,
    substitute_subterm(ToBeSubst, Replacer, Psi, Result),!.
substitute_subterm(ToBeSubst, Replacer, exists([Vars],Phi), exists([Vars],Newphi)) :-
    substitute_subterm(ToBeSubst, Replacer, Phi, Newphi).

sub_formula([], [], Result, Result).
sub_formula([FirstSubst|Rest], [FirstReplacer|RestReplacer], Formula, SubFormula) :-
    substitute_subterm(FirstSubst, FirstReplacer, Formula, InterimFormula),
    sub_formula(Rest, RestReplacer, InterimFormula, SubFormula).


/* Get the slfp-formula which will be transformed into lfp-form*/
getInitialToBeSubstPreds(Pred, Preds,SlfpFormulas, RelvHeadPreds, SearchedFormula) :-
    getRelevantFormula(Pred, Preds, SlfpFormulas, SearchedFormula),
    getRelevantSubterms(Pred, Preds, SearchedFormula, SearchedLiterals),
	maplist(headpred_in_literal, SearchedLiterals, RelvHeadPreds).
    

/* Get all elements which are on the left side of the element and put them in LeftElems */
getLeftSideElements(_, _, [], []).
getLeftSideElements(Elem, ElemList, [FirstElem|RestElem], LeftElems) :-
    nth0(RelvIndex, ElemList, Elem),
    nth0(Index, ElemList, FirstElem),
    Index < RelvIndex,
    append([FirstElem], Out, LeftElems),
    getLeftSideElements(Elem, ElemList, RestElem, Out).
getLeftSideElements(Elem, ElemList, [FirstElem|RestElem], LeftElems) :-
    nth0(RelvIndex, ElemList, Elem),
    nth0(Index, ElemList, FirstElem),
    Index >= RelvIndex,
    append([], Out, LeftElems),
    getLeftSideElements(Elem, ElemList, RestElem, Out).

/* RightElems is a list of predicates that are on the right side
 * of the element */
getRightSideElements(Elem, ElemList, RightElems) :-
    getLeftSideElements(Elem, ElemList,ElemList, LeftElems),
    subtract(ElemList, [Elem], WithoutElem),
    subtract(WithoutElem, LeftElems, RightElems).

/* Used to build lfp-formula from the right-side to the left
 * The former slfp-formula will be replaced with its lfp-formula in the list SlfpFormulas
 * The substitution is done in the new_build_lfp1 predicate */
get_lfp([], _, _, []).
get_lfp([FirstPred|RestPred], Preds, SlfpFormulas, ChangedSlfp) :-
    getRelevantFormula(FirstPred, Preds, SlfpFormulas, SearchedFormula),
    getInitialToBeSubstPreds(FirstPred, Preds, SlfpFormulas, RelvHeadPreds, SearchedFormula),
    getRightSideElements(FirstPred, Preds, RightSidePreds),
    intersection(RightSidePreds, RelvHeadPreds, IntersectionPreds),
    new_build_lfp1(FirstPred, Preds, IntersectionPreds, SlfpFormulas, LFPForm),
    reduced_form(LFPForm, ReducedForm),
    build_lfp_constructor(FirstPred, ReducedForm,NewLfpForm),
    select(SearchedFormula, SlfpFormulas, NewLfpForm, NewSlfp),
    append([NewLfpForm], Out, ChangedSlfp),
    get_lfp(RestPred, Preds, NewSlfp,Out),!.


/*Kommt Pred in der Formel vor? */
/*Reduced Formula nach dem Einsetzen drüber laufen lassen*/
build_lfp_constructor(Pred, exists(Boundvars, Phi), lfp(Pred, exists(Boundvars, Phi))) :-
	sub_term(Pred, Phi).
build_lfp_constructor(Pred, Phi, lfp(Pred, Phi)) :-
	sub_term(Pred, Phi),
    Phi \= exists(_,_).
build_lfp_constructor(Pred, Phi, Phi) :-
	\+sub_term(Pred, Phi).


/* Used to build lfp-formula by substituting in formulas
 * This is done recursively */
new_build_lfp1(Pred, Preds, [], Slfp, SearchedFormula) :-
    getRelevantFormula(Pred, Preds, Slfp, SearchedFormula).
new_build_lfp1(Pred, Preds, ToBeSubstPreds, Slfp, FlatSubFormula) :-
    ToBeSubstPreds \= [],
    length(ToBeSubstPreds, LenForPreds),
    copy_list([Preds], LenForPreds, EnoughPreds),
    copy_list([Slfp], LenForPreds, EnoughSlfp),
    maplist(getRelevantFormula, ToBeSubstPreds, EnoughPreds, EnoughSlfp, SearchedFormulas),
    getRelevantFormula(Pred, Preds, Slfp, SearchedFormula),
    getRelevantSubterms(Pred, ToBeSubstPreds, SearchedFormula, SearchedLiterals),
    maplist(variables_in_literal, SearchedLiterals, ReplacerVars),
    NestedSearchedLiterals = [SearchedLiterals],
    maplist(getFreeVarsOfFormula, SearchedFormulas, SearchedFreevars),
    maplist(substitute_formula, SearchedFreevars, ReplacerVars, SearchedFormulas, New),
    maplist(sub_formula, NestedSearchedLiterals, [New], [SearchedFormula]
            , SubFormula),
    flatten1(SubFormula, FlatSubFormula).

/* Auxilary predicate to get the freevars of a lfp-formula */
getFreeVarsOfFormula(Phi, Freevars) :-
    Phi \= lfp(_,_),
    freevars(Phi, Freevars).
getFreeVarsOfFormula(lfp(_, Phi), Freevars) :-
    freevars(Phi, Freevars).



/* Returns the lfp-Formula of the Pred
 * Every formula which is on the right-hand side will considered for substituiting in */
new_lfp(Pred, Preds, SlfpFormulas, SearchedLfp) :-
    reverse(Preds, ReversedPreds),
    get_lfp(ReversedPreds, Preds, SlfpFormulas, ReversedAllLfps),
    reverse(ReversedAllLfps, AllLfps),
    getRelevantFormula(Pred, Preds, AllLfps, SearchedLfp),!.
    

/*Auxilary predicate to check if it is a subatom*/
sub_atom1(Subatom, Atom) :-
    sub_atom(Atom,_,_,_,Subatom).

/* Extracts the headpredicate of a literal */
headpred_in_literal(Pred-_, Pred).

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
    max_list(Lens, Max).

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
    maplist(headpred_in_literal, RelvLiterals, Preds),
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
 * NewResult should be reduced as much as possible */
isfr1(0,_,_,_,Term,ReducedTerm) :-
    reduced_form(Term, ReducedTerm).
isfr1(Iter, Counter, Term, Pred, PrevResult, ReducedQuantTerm) :-
    Iter > 0,
    Counter >= 0,
    NewCounter is Counter + 1,
    reduced_form(PrevResult, ReducedPrevResult),
    getBoundVarsOfFormula(Term, Boundvars),
    length(Boundvars, LenBoundvars),
    copy_list([NewCounter], LenBoundvars, EnoughIterIndices),
    maplist(atom_concat, Boundvars, EnoughIterIndices, NewBoundvars),
    freevars(ReducedPrevResult, FreevarsPrevResult),
    find_relv_literal(Term, Pred, Literal),
    Literal \= [],
    variables_in_literal(Literal, LiteralVars),
    replace_vars(Boundvars, NewBoundvars, ReducedPrevResult,NewPrevResult),
    substitute_formula(FreevarsPrevResult, LiteralVars, NewPrevResult, NewPrevResult1),
    term_to_atom(Term, AtomFormula),
    term_to_atom(Literal, AtomLiteral),
    term_to_atom(NewPrevResult1, AtomNewPrevResult),
    replace_nth_word(AtomFormula,1,AtomLiteral, AtomNewPrevResult, InterResult),
    term_to_atom(ReplacedTerm, InterResult),
    reduced_form(ReplacedTerm, ReducedTerm),
    reduced_quant_elim(ReducedTerm, ReducedQuantTerm),
    %ReducedQuantTerm == ReducedPrevResult,!.
    transform_term(ReducedQuantTerm, ReducedPrevResult, TransfTerm),
    terminate_isfr(TransfTerm),!.
%Abbruch mit notsat an dieser Stelle
isfr1(Iter, Counter, Term, Pred, PrevResult, NewResult) :-
    Iter > 0,
    Counter >= 0,
    NewCounter is Counter + 1,
    NewIter is Iter - 1,
    reduced_form(PrevResult, ReducedPrevResult),
    getBoundVarsOfFormula(Term, Boundvars),
    length(Boundvars, LenBoundvars),
    copy_list([NewCounter], LenBoundvars, EnoughIterIndices),
    maplist(atom_concat, Boundvars, EnoughIterIndices, NewBoundvars),
    freevars(ReducedPrevResult, FreevarsPrevResult),
    find_relv_literal(Term, Pred, Literal),
    Literal \= [],
    variables_in_literal(Literal, LiteralVars),
    replace_vars(Boundvars, NewBoundvars, ReducedPrevResult,NewPrevResult),
    substitute_formula(FreevarsPrevResult, LiteralVars, NewPrevResult, NewPrevResult1),
    term_to_atom(Term, AtomFormula),
    term_to_atom(Literal, AtomLiteral),
    term_to_atom(NewPrevResult1, AtomNewPrevResult),
    replace_nth_word(AtomFormula,1,AtomLiteral, AtomNewPrevResult, InterResult),
    term_to_atom(ReplacedTerm, InterResult),
    reduced_form(ReplacedTerm, ReducedTerm),
    reduced_quant_elim(ReducedTerm, ReducedQuantTerm),
    %ReducedQuantTerm \= ReducedPrevResult,
    transform_term(ReducedQuantTerm, ReducedPrevResult, TransfTerm),
    \+terminate_isfr(TransfTerm),
    isfr1(NewIter, NewCounter, Term, Pred, ReducedQuantTerm or ReducedPrevResult, NewResult),!.
isfr1(Iter, Counter, Term, Pred, _, ReducedQuantTerm) :-
    Iter > 0,
    Counter >= 0,
    reduced_form(Term, ReducedTerm),
    reduced_quant_elim(ReducedTerm, ReducedQuantTerm),
    find_relv_literal(Term, Pred, Literal),
    Literal == [].




/* Auxilary predicate to replace list of variables */
replace_vars(_,_,false,false).
replace_vars([],_,Term,Term).
replace_vars([],[],Term, Term).
replace_vars([FirstVars|RestVars], [FirstNVars|RestVars], Term, NewTerm) :-
    replace(FirstVars, FirstNVars, Term, FirstNewTerm),
    replace_vars(RestVars, RestVars, FirstNewTerm, NewTerm).

/* Auxilary predicate to find relevant literals in a term */
find_relv_literal(Term,Pred, Literal) :-
    findall(Value, sub_term(Value, Term), SubTermList),
    include(getLiteral, SubTermList, Literals), 
    include(checkPredLiteral(Pred), Literals, RelvLiteral),
    flatten1(RelvLiteral, Literal).

/* Extracts the IterNumber of the AlphaFormula */
get_iter_number(Term,1,Term) :-
    term_to_atom(Term, AtomTerm),
    \+sub_atom1('alpha', AtomTerm).
get_iter_number(AlphaFormula,IterNumber,Term) :-
    AlphaFormula =.. Formula,
    nth0(0,Formula,Alpha),
    nth0(2, Formula, Term),
    split_string(Alpha, "_", "", Split),
    subtract(Split, ["alpha"], Result),
    flatten1(Result, IterString),
    number_string(IterNumber, IterString).

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
replace_rec(NewForm, [],[], NewForm).
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
    copy_list(Boundvars, LenFreevars, EnoughBoundvars),
    copy_list([InnerFormula], LenFreevars, EnoughFormulas),
    seperate_elems_in_a_list(EnoughBoundvars, Sep1),
    seperate_elems_in_a_list(Freevars, Sep2),
    maplist(substitute_formula, Sep1, Sep2, EnoughFormulas, Res).

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
build_dnf_rec(Phi and Psi,Phi_r and Psi_r) :-
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
    %FlatFreeElems sind die fep
    maplist(flatten, FreeElems, FlatFreeElems),
    %NonFreeElems sind die non-fep
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
    %maplist(length, NonFreeElems, LenNonFreeElems),
    filter_negated_parts(NonFreeElems, NegatedNonFreeElems),
    maplist(exclude(notsath), NonFreeElems, SatNegatedNonFreeElems),
    maplist(include(notsath), NonFreeElems, NotSatNegatedNonFreeElems),
    maplist(length, SatNegatedNonFreeElems, LenSatNegatedNonFreeElems),
    maplist(length, NotSatNegatedNonFreeElems, LenNotSatNegatedNonFreeElems),
    maplist(copy_list([true]), LenSatNegatedNonFreeElems, EnoughTrue),
    maplist(copy_list([false]), LenNotSatNegatedNonFreeElems, EnoughFalse),
    maplist(replace_rec, InnerPart, SatNegatedNonFreeElems, EnoughTrue, NewInnerPart),
    maplist(replace_rec, NewInnerPart, NotSatNegatedNonFreeElems, EnoughFalse,
            NewInnerPartNegatedMapped),
    maplist(subtract, NonFreeElems, NegatedNonFreeElems, NormalNonFreeElems),
    maplist(length, NormalNonFreeElems, LenNormalNonFreeElems),
    maplist(copy_list([true]), LenNormalNonFreeElems, EnoughNormalTrue),
    maplist(replace_rec, NewInnerPartNegatedMapped, NormalNonFreeElems, EnoughNormalTrue,
            FinalNewInnerPart),
    flatten(FinalNewInnerPart,FlatNewInnerPart),
    maplist(split_term, FlatNewInnerPart, SplitInnerPart),
    flatten(SplitInnerPart, FlatInnerPart).
helper_map_non_fep(forall(Boundvars, _, Literals),FlatInnerPart) :-
    maplist(list_to_conj,Literals, InnerPart),
    length(InnerPart, LenInnerPart),
    copy_list([Boundvars], LenInnerPart, EnoughBoundvars),
    maplist(is_free_elem_part, EnoughBoundvars, Literals, FreeElems),
    maplist(flatten, FreeElems, FlatFreeElems),
    maplist(subtract, Literals, FlatFreeElems, NonFreeElems),
    maplist(length, NonFreeElems, LenNonFreeElems),
    maplist(copy_list([false]), LenNonFreeElems, EnoughTrue),
    maplist(replace_rec, InnerPart, NonFreeElems, EnoughTrue, NewInnerPart),
    flatten(NewInnerPart,FlatNewInnerPart),
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
    term_to_atom(Term, AtomTerm),
    maplist(term_to_atom, FlatRelv, RelvAtoms),
    maplist(term_to_atom, FlatNew, FlatNewAtoms),
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
addnot(Part, not(Part)).

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
    maplist(addnot,FlatSplit, NotList),
    list_to_conj(NotList, NotConj),
    flatten1(NotConj, FlatNotConj),!.

/* Termination condition for the isfr */
terminate_isfr(TransfTerm) :-
    while_dnf(TransfTerm,Dnf),
    split_term_at_or(Dnf,SplitTerm),
	flatten(SplitTerm, FlatSplitTerm),
	maplist(split_term, FlatSplitTerm, SplitConjs),
	maplist(flatten, SplitConjs, FlatSplitConjs),
	maplist(notsat, FlatSplitConjs),!.

stratify(Program,Predicates,Strata) :-
    length(Strata,N),
    Strata ins 0..N,
    stratification(Program,Predicates,Strata).

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

/* Computes the lfp-formula for a a predicate (without any replacements) */
compute_lfp(Program,Pred,Lfp,RelvFreeVars) :-
 datalog_to_formula(Program-Pred,[[a,b,c]], slfp(Preds, Slfp,FreeVars)),
 nth1(Index, Preds, Pred),
 nth1(Index, FreeVars, RelvFreeVars),
 nth1(Index, Slfp, RelvForm),
 new_lfp(Pred, [Pred],[RelvForm], Lfp).

/* Helper predicates for computing replacer predicates*/
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
    intensionals(Program, HeadPreds),
	bodyPreds(Program, BodyPreds),
	append(HeadPreds, BodyPreds, AllPreds),
    sort(AllPreds, SortedAllPreds),
    once(stratify(Program,SortedAllPreds,Strata)),
	once(labeling([],Strata)).

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
    %sort(Literals, SortedLiterals),
    include(checkPredLiteral(FirstPred), Literals, RelvLiterals),
    compute_replacer(RelvLiterals, CurrLfp, Replacers),
    maplist(variables_in_literal, RelvLiterals, RelvVars),
    maplist(variables_in_literal, Replacers, ReplVars),
    maplist(reduced_form, Replacers, RedReplacers),
    maplist(substitute_literal, ReplVars, RelvVars, RedReplacers, NewReplacers),
    replace_rec(NextLfp, RelvLiterals, NewReplacers, ReplForm),
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

/* Looks in a lfp-formula if there are predicates which can be replaced and computes the replacers */
look_for_repl_literals([], _,_, _, RelvForm,RelvForm).
look_for_repl_literals([FirstRemPred|RestRemPred], Preds,Lfps, SortedLiterals, RelvForm, NewForm) :-
    include(checkPredLiteral(FirstRemPred), SortedLiterals, RelvLiterals),
    nth1(Index,Preds,FirstRemPred),
    nth1(Index,Lfps, Repl),
    compute_replacer(RelvLiterals, Repl, Replacers),
    maplist(variables_in_literal, RelvLiterals, RelvVars),
    maplist(variables_in_literal, Replacers, ReplVars),
    maplist(substitute_literal, ReplVars, RelvVars, Replacers, NewReplacers),
    replace_rec(RelvForm, RelvLiterals, NewReplacers, ReplForm),
    look_for_repl_literals(RestRemPred, Preds,Lfps, SortedLiterals, ReplForm, NewForm).

/* Computes recursively all lfp-formulas of a logic program */
compute_rec_lfp(_,[],[]).
compute_rec_lfp(Program, [FirstPred,SecPred|RestPred],AllLfps) :-
    intensionals(Program, Int),
    \+member(FirstPred, Int),
    compute_rec_lfp(Program,[SecPred|RestPred],AllLfps).
compute_rec_lfp(Program, [FirstPred|RestPred],AllLfps) :-
    intensionals(Program, Int),
    member(FirstPred, Int),
    compute_lfp(Program, FirstPred, FirstLfp, _),
    append([FirstLfp], Out, AllLfps),
    compute_rec_lfp(Program, RestPred, Out).

/* Computes the Lfp-formula of a logic program which contains negative predicates */
compute_for_negation(Program, Pred,SubVars,RelvFreeVars,FinalLfp) :-
    datalog_to_formula(Program-Pred,SubVars,slfp(Preds,_,FreeVars)),
    compute_strata(Program, Strata, OrderPreds),
    compute_order_preds(Strata, OrderPreds, AscOrdPreds),
    compute_rec_lfp(Program, AscOrdPreds, Lfps),
    intensionals(Program, Intensionals),
    intersection(AscOrdPreds, Intensionals, IntersecPreds),
    do_replacement1(IntersecPreds,IntersecPreds, Lfps, FinalLfps),
    nth1(Index, IntersecPreds,Pred),
    nth1(Index,FinalLfps, FinalLfp),
    nth1(Index1, Preds, Pred),
    nth1(Index1, FreeVars, RelvFreeVars).

/* Computes the Lfp-formula of a logic program with only positive predicates */
compute_for_pos(Program, Pred,SubVars,RelvFreeVars,FinalLfp) :-
    datalog_to_formula(Program-Pred,SubVars, slfp(Preds,_,FreeVars)),
    reverse(Preds, RevPreds),
	compute_rec_lfp(Program, RevPreds, Lfps),
    intensionals(Program, Intensionals),
    intersection(RevPreds, Intensionals, IntersecPreds),
    do_replacement1(IntersecPreds,IntersecPreds, Lfps, FinalLfps),
    nth1(Index, IntersecPreds,Pred),
    nth1(Index,FinalLfps, FinalLfp),
   	nth1(Index1, Preds, Pred),
    nth1(Index1, FreeVars, RelvFreeVars).

/* A logic program is asymptotically transformed into a det. logic program */
compute_lp_form(Program, Pred, SubVars,DetLp) :-
    contains_term(not(_), Program),
    compute_for_negation(Program, Pred,SubVars,Freevars, Lfp),
    compute_alpha(Lfp, _, _,AlphaConstr),
	replace_lfps(Lfp, AlphaConstr, AlphaForm),
	get_iter_number(AlphaForm, Iter,InnerForm),
	isfr1(Iter,0,InnerForm,[Pred],false,ReducedInnerForm),
	convert_to_lp(Pred,Freevars, ReducedInnerForm, DetLp),!.
compute_lp_form(Program, Pred,SubVars,DetLp) :-
    \+contains_term(not(_), Program),
    compute_for_pos(Program, Pred, SubVars,Freevars,Lfp),
    compute_alpha(Lfp, _, _,AlphaConstr),
	replace_lfps(Lfp, AlphaConstr, AlphaForm),
	get_iter_number(AlphaForm, Iter,InnerForm),
	isfr1(Iter,0,InnerForm,[Pred],false,ReducedInnerForm),
	convert_to_lp(Pred,Freevars, ReducedInnerForm, DetLp),!.

/* Checks if a list only contains the same elements */
same([]).
same([_]).
same([X,X|T]) :- same([X|T]).

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

duplicates([],[]).
duplicates([X|Xs], [X|Ys]) :-
    member(X, Xs),
    delete(Xs, X, XsWithoutX),
    duplicates(XsWithoutX, Ys).

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
    

count_dupl_occurr([],_,[]).
count_dupl_occurr([FirstDupl|RestDupl], Vars, Occurr) :-
    occurrences_of_var(FirstDupl, Vars, Count),
    append([Count], Out, Occurr),
    count_dupl_occurr(RestDupl, Vars, Out).

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

%%%%% Hier weiter machen, um same zu bilden
create_util_pred_same([],_,[]).
create_util_pred_same([FirstVar|RestVar], ReplVars, Preds) :-
  include(sub_atom1(FirstVar), ReplVars, Atoms),
  create_same_pred(Atoms, Sames),
  append(Sames, Out, Preds),
  create_util_pred_same(RestVar, ReplVars, Out).

create_same_pred([], []).
create_same_pred([First|Rest], Sames) :-
    helper_create_pred(First,Rest, FirstSamePred),
    append(FirstSamePred,Out, Sames),
    create_same_pred(Rest,Out).

helper_create_pred(_, [], []).
helper_create_pred(Elem, [X|Xs], Preds) :-
    Pred = same-[Elem,X],
    append([Pred], Out, Preds),
    helper_create_pred(Elem,Xs,Out).
    

removehead([_|Rest], Rest).
removetail([], []).
removetail([X|_], [X]).
