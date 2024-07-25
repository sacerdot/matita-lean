import Lean -- To allow Ctrl+Click over Lean syntax
import Verbose.English.All

open Lean
open Lean.Elab.Tactic

namespace matita

-- Bugs:
--  assume/suppose fanno anche change per via di Verbose

-- Todo:
--  it suffices to prove
--  eliminazione and/exists/iff
--  introduzione and/iff
--  we decide to prove
--  we proceed by cases
--  eliminazione dell'assurdo
--  suppose ... that is equivalent to

-- Ugly:
--  code duplication for empty matitaJust
--  code duplication for omitting name of hypothesis in "we proved"

-- Implemented:
--  assume
--  suppose
--  done
--  we proved
--  we need to prove
--  we claim ... as ... by ...

syntax "assume " ident " : " term : tactic

macro_rules
  | `(tactic| assume $ident : $type) => `(tactic| Fix₁ $ident:ident : $type)

syntax "suppose " term (" as " ident)? : tactic

macro_rules
  | `(tactic| suppose $term as $ident) => `(tactic| Assume₁ $ident:ident : $term)
  | `(tactic| suppose $term) => `(tactic| intro)


syntax "_last_hypothesis_" : term

/-elab_rules : term
 |`(term| _last_hypothesis_) => do
    let x := (← Lean.getLCtx).lastDecl.map (fun x ↦ x.toExpr)
    Lean.addRawTrace x
    x -/

elab_rules : term
 |`(term| _last_hypothesis_) => do (← Lean.getLCtx).lastDecl.map (fun x ↦ x.toExpr) -- bug here exclude recursive call to theorem

-- one more bug here
--macro_rules
--  | `(matitaJust | by ) =>
--    `(Lean.Parser.Tactic.SolveByElim.arg | [])

declare_syntax_cat matitaJust

syntax "thus "? ("by " ident,+)? : matitaJust

def matitaJust_to_solveByElimArg : TSyntax `matitaJust -> MacroM (TSyntax ``Lean.Parser.Tactic.SolveByElim.args)
  | `(matitaJust | thus by $[$terms],* ) => do
    let args ← terms.mapM fun x => `(Lean.Parser.Tactic.SolveByElim.arg| $x:ident)
    `(Lean.Parser.Tactic.SolveByElim.args| [$(args.push (← `(Lean.Parser.Tactic.SolveByElim.arg| _last_hypothesis_))),*])
  | `(matitaJust | by $[$terms],* ) =>
    `(Lean.Parser.Tactic.SolveByElim.args| [$[$terms:ident],*])
  | `(matitaJust | thus ) =>
    `(Lean.Parser.Tactic.SolveByElim.args| [_last_hypothesis_])
--  | `(matitaJust | ) =>
--    `(Lean.Parser.Tactic.SolveByElim.args| [])
  | _ => -- panic! "xxx" -- thereis  the right throwXXX
    `(Lean.Parser.Tactic.SolveByElim.args| [])

syntax matitaJust " done" : tactic

macro_rules
  | `(tactic | $mj:matitaJust done) => do
    `(tactic | solve_by_elim only $(← matitaJust_to_solveByElimArg mj))
  | `(tactic | done) => do
    `(tactic | solve_by_elim only [])

syntax (matitaJust)? " we " " proved " term (" as " ident)? : tactic

-- duplicated code, not nice
macro_rules
  | `(tactic | $mj:matitaJust we proved $term as $ident) => do
    let x ← matitaJust_to_solveByElimArg mj
    `(tactic | have $ident : $term := by solve_by_elim only $x)
  | `(tactic | $mj:matitaJust we proved $term) => do
    let x ← matitaJust_to_solveByElimArg mj
    `(tactic | have _ : $term := by solve_by_elim only $x)
  | `(tactic | we proved $term as $ident) =>
    `(tactic | have $ident : $term := by solve_by_elim only [])
  | `(tactic | we proved $term) =>
    `(tactic | have _ : $term := by solve_by_elim only [])

declare_syntax_cat matitaEquivalent

syntax "that " "is " "equivalent " "to " term : matitaEquivalent

syntax "we " "need " "to " "prove " term (matitaEquivalent)? : tactic

macro_rules
 | `(tactic | we need to prove $term) =>
  `(tactic | guard_target =ₛ $term)
 | `(tactic | we need to prove $exp that is equivalent to $inf) =>
  `(tactic | guard_target =ₛ $exp <;> change $inf)

/-

elab_rules : tactic
 |`(tactic| then) =>
   withMainContext do
    let x := (← getMainDecl).lctx.lastDecl.map (fun x ↦ x.toExpr)
    Lean.addRawTrace x -/

/-macro_rules
 | `(tactic|then) =>
  `(tactic| trace "ciao") -/

macro "we " "claim " stmt:term "as " name:ident "by" colGt prf:tacticSeq : tactic => `(tactic|have $name : $stmt := by $prf)
macro "we " "claim " stmt:term                  "by" colGt prf:tacticSeq : tactic => `(tactic|have _ : $stmt := by $prf)

end matita

-- By ax_inclusion2 it suffices to prove that ∀Z, Z ∈ A → Z ∈ A

namespace set_theory

/- set, ∈ -/
axiom set: Type
axiom mem: set → set → Prop

infix:50 (priority := high) " ∈ " => mem

-- Extensionality
axiom ax_extensionality: ∀A B, (∀Z, Z ∈ A ↔ Z ∈ B) → A = B

-- Inclusion
def incl (A:set) (B:set) : Prop :=
 ∀Z, Z ∈ A → Z ∈ B

infix:50 (priority := high) " ⊆ " => incl

-- Emptyset  ∅
axiom emptyset: set
notation:max "∅" => emptyset
axiom ax_empty: ∀X, (X ∈ ∅)→ False

-- Intersection ∩
axiom intersect: set → set → set
infix:80 (priority := high) " ∩ " => intersect
axiom ax_intersect1: ∀A B, ∀Z, (Z ∈ A ∩ B → Z ∈ A ∧ Z ∈ B)
axiom ax_intersect2: ∀A B, ∀Z, (Z ∈ A ∧ Z ∈ B → Z ∈ A ∩ B)

-- Proofs in matita
namespace matita

theorem reflexivity_inclusion: ∀A, A ⊆ A := by
 assume A: set
 we need to prove A ⊆ A that is equivalent to ∀Z, Z ∈ A → Z ∈ A
 assume Z: set
 suppose Z ∈ A
 thus done

theorem empty_absurd: ∀X A, X ∈ ∅ → X ∈ A := by
 assume X : set
 assume A : set
 suppose X ∈ ∅
 thus by ax_empty done

theorem intersection_idempotent: ∀A, A ∩ A = A := by
 assume A : set
 By ax_extensionality it suffices to prove ∀Z, Z ∈ A ∩ A ↔ Z ∈ A
 assume Z : set
 apply Iff.intro -- ???
 . suppose Z ∈ A ∩ A
   thus by ax_intersect1 we proved Z ∈ A ∧ Z ∈ A
   thus by And.left done
 . suppose Z ∈ A
   thus by ax_intersect2 done

end matita

-- Proofs in Lean/verbose-lean

-- procedural proof
theorem reflexivity_inclusion: ∀A, A ⊆ A := by
 intro A
 whnf
 intro Z
 intro H
 apply H

-- declarative proof, explicit hypotheses
theorem reflexivity_inclusion2: ∀A, A ⊆ A := by
 Fix A -- or Fix A : set
 whnf -- ??
 Fix Z
 Assume HA : Z ∈ A
 We conclude by HA

-- declarative proof, implicit hypotheses
theorem reflexivity_inclusion3: ∀A, A ⊆ A := by
 Fix A -- or Fix A : set
 whnf -- ??
 Fix Z
 Assume HA : Z ∈ A
 Since Z ∈ A we conclude that Z ∈ A

theorem empty_absurd: ∀X A, X ∈ ∅ → X ∈ A := by
 Fix X A
 Assume H: X ∈ ∅
 By ax_empty applied to X using H we get K: False
 Let's prove it's contradictory
 We conclude by K

end set_theory

/-


notation "'ABSURDUM' A" non associative with precedence 89 for @{'absurdum $A}.
interpretation "ex_false" 'absurdum A = (False_ind ? A).

(* Da qui in avanti riempite i puntini e fate validar quello che scrivete
   a Matita usando le icone con le frecce. *)

(* Exercise 1 *)
theorem reflexivity_inclusion: ∀A. A ⊆ A.
 assume A:set (* Ora dobbiamo dimostrare A ⊆ A, guarda il goal in alto a destra, è cambiato! *)
 we need to prove (∀Z. Z ∈ A → Z ∈ A) (ZA_to_ZA) (* da ora stiamo provando 'ZA_to_ZA' (guarda in alto a destra (Matita ha aggiunto un altra finestrella di dimostrazione), fino al relativo 'done' *)
  assume Z:(*BEGIN*)set(*END*)
  suppose (Z ∈ A) (ZA)
  by ZA done
  (* fine della prova di 'ZA_to_ZA' (guarda in alto a destra, Matita ha chiuso la finestrella di dimostrazione che aveva aperto),
     ora l'abbiamo guadagnata tra le ipotesi (ora compare nella lista in alto a destra)!
   Continuiamo con la prova del nostro teorema *)
 by ax_inclusion2, (*BEGIN*) ZA_to_ZA (*END*) done (* Quale ipotesi devo combinare con l'assioma? *)
qed.
-/

/-
(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)
(*DOCBEGIN

Cosa fare e come consegnare
===========================

Scaricate il file exercise-set_theory.ma (usando il pulsante destro sul link e selezionando `Save link as' o qualcosa di simile). Poi aprite il file salvato lanciando un terminale e lanciando il comando `matita exercise-set_theory-2023-09-26.ma' dalla directory in cui l'avete salvato.

Per prima cosa all'inizio del file riempite i campi con i vostri nomi, cognomi e numero di matricole.

Durante la prova ricordatevi di salvare costantemente per non perdere il lavoro in caso di crash. Matita fa dei salvataggi automatici, ma non fidatevi.

Alla fine dell'esercitazione o del tempo consegnate il file con il comando `~sacerdot/logica2223/ConsegnaLogica exercise-set_theory-2023-09-26.ma'.


Come scrivere i simboli
=======================

Per inserire i simboli matematici è necessario digitare il loro nome
e poi premere ALT-L. In generale i nomi dei simboli sono della forma
`\nome`, ad esempio `\equiv`. Alcuni simboli molto frequenti hanno
dei sinonimi più comodi da digitare, per esemio `⇒` ha sia il nome
`\Rightarrow` sia `=>`.

Segue un elenco dei simboli più comuni e i loro nomi separati da virgola,
Se sono necessari dei simboli non riportati di seguito si può visualizzare
l'intera lista dal menù a tendina `View ▹ TeX/UTF8 table`.

* `∨` : `\or`
* `∧` : `\and`
* `¬` : `\lnot`
* `→` : `\to`, `->`
* `⇔` : `\iff`
* `∀` : `\forall`
* `∈` : `\in`
* `∪` : `\cup`
* `∩` : `\cap`
* `∅` : `\empty`
* `⊆` : `\sube`

La sintassi `∀x.P` significa "per tutti gli `x` vale `P`".

La sintassi `F → G` dove `F` e `G` sono proposizioni nel metalinguaggio
significa "`F` implica `G`". Attenzione, il simbolo `⇒` (usato a lezione)
non ha lo stesso significato in Matita.

La sintassi `ℕ → ℕ` è il tipo delle funzioni che preso un numero naturale
restituiscono un numero naturale.

Tutti gli operatori sono associativi a sinistra, tranne `→'.

DOCEND*)
(*DOCBEGIN

Il linguaggio di dimostrazione di Matita
========================================

Gli esercizi di questa lezione richiedono di scrivere una dimostrazione.
Tale dimostrazionedeve essere scritta utilizzando
il linguaggio di dimostrazione di Matita.
Tale linguaggio è composto dai seguenti comandi:

* `assume nome : tipo`

  Quando si deve dimostrare un tesi come `∀F : Formula.P`, il comando
  `assume F : Formula` fissa una generica `Formula` `F` e la tesi
  diventa `P` dove `F` è fissata.

* `suppose P (nome)`

  Quando si deve dimostrare una tesi come `P → Q`, il comando
  `suppose P (Ipotesi1)` da il nome `Ipotesi1` a `P` e cambia la tesi
  `Q`, che ora può essere dimostrata facendo riferimento all'assunzione
  `P` tramite il nome `Ipotesi1`.

* `we procede by cases on x to prove Q`

  Si usa quando si vuole usare una disgiunzione per dimostrare una proposizione Q.
  `x` deve essere il nome di una disgiunzione nelle ipotesi del goal corrente.

* `case name`

  Nelle prove per induzione o per casi, ogni caso deve iniziare con il
  comando `case nome`, ad esempio se si procede per casi su una disgiunzione
  si dovrà analizzare prima il caso in cui sia vera la sottoformula sinistra e
  poi il caso in cui sia vera la formula di destra; in entrambi i casi la
  sottodimostrazione comincierà con `case nome.` dove `nome` serve come
  chiarimento all'utente.

* `by name1,name2,... we proved P (name)`

  Permette di ottenere una nuova ipotesi `P` chiamandola `name` utilizzando
  le ipotesi `name1`,`name2`... bisogna prestare attenzione a elencare tutte le ipotesi
  necessarie (assiomi, ipotesi, regole dei connettivi, eventuali teoremi).

* `by name1,name2,... done`

  Termina un caso della dimostrazione se quello che dobbiamo dimostrare è una banale conseguenza delle ipotesi `name1`,`name2`,...

* `by name we have F1 (name1) and F2 (name2)`

  Quando `name` è una ipotesi del tipo `F1 ∧ F2`, si ottengono due nuove ipotesi chiamate `name1` e `name2` di tipo rispettivamente `F1` e `F2`.

* `we need to prove F (name)`

  Inizia una sotto-dimostrazione di `F`. Una volta conclusa, si riprende la dimostrazione precedente con in più l'ipotesi `name` che `F` valga.

* `using (ABSURDUM name) done`

  Conclude la dimostrazione quando `name` è l'ipotesi che `False` valga

Teoremi e assiomi
========================================

Per concludere le dimostrazioni potete utilizzare i seguenti assiomi e teoremi

* conj: ∀A, B. A → B → A ∧ B
* conj: ∀A, B. (A → B) → (B → A) → A ⇔ B
* or_introl: ∀A, B. A → A ∨ B
* or_intror: ∀A, B. B → A ∨ B
* ax_extensionality: ∀A, B. (∀Z. Z ∈ A ⇔ Z ∈ B) → A = B
* ax_inclusion1: ∀A, B. A ⊆ B → (∀Z. Z ∈ A → Z ∈ B)
* ax_inclusion2: ∀A, B. (∀Z. Z ∈ A → Z ∈ B) → A ⊆ B
* ax_empty: ∀X. ¬(X ∈ ∅)
* ax_intersect1: ∀A,B. ∀Z. (Z ∈ A ∩ B → Z ∈ A ∧ Z ∈ B)
* ax_intersect2: ∀A,B. ∀Z. (Z ∈ A ∧ Z ∈ B → Z ∈ A ∩ B)
* ax_union1: ∀A,B. ∀Z. (Z ∈ A ∪ B → Z ∈ A ∨ Z ∈ B)
* ax_union2: ∀A,B. ∀Z. (Z ∈ A ∨ Z ∈ B → Z ∈ A ∪ B)

DOCEND*)


(*

 Componenti del gruppo (completare):

 * Nome1: ...
 * Cognome1: ...
 * Numero di matricola1: ...

 * Nome2: ...
 * Cognome2: ...
 * Numero di matricola2: ...

*)

(* Saltate le righe seguenti dove vengono dati gli assiomi e definite
   le notazioni e cercate Exercise 1. *)

include "basics/logic.ma".
include "basics/core_notation.ma".

notation "hvbox(A break ⇔ B)" left associative with precedence 30 for
@{'iff $A $B}.
interpretation "iff" 'iff A B = (iff A B).

(* set, ∈ *)
axiom set: Type[0].
axiom mem: set → set → Prop.
axiom incl: set → set → Prop.

notation "hvbox(a break ∈ U)" non associative with precedence 50 for
@{'mem $a $U}.
interpretation "mem" 'mem = mem.

notation "hvbox(a break ⊆ U)" non associative with precedence 50 for
@{'incl $a $U}.
interpretation "incl" 'incl = incl.

(* Extensionality *)
axiom ax_extensionality: ∀A, B. (∀Z. Z ∈ A ⇔ Z ∈ B) → A = B.

(* Inclusion *)
axiom ax_inclusion1: ∀A, B. A ⊆ B → (∀Z. Z ∈ A → Z ∈ B).
axiom ax_inclusion2: ∀A, B. (∀Z. Z ∈ A → Z ∈ B) → A ⊆ B.

(* Emptyset  ∅ *)
axiom emptyset: set.

notation "∅" non associative with precedence 90 for @{'emptyset}.
interpretation "emptyset" 'emptyset = emptyset.

axiom ax_empty: ∀X. (X ∈ ∅)→ False.

(* Intersection ∩ *)
axiom intersect: set → set → set.

notation "hvbox(A break ∩ B)" left associative with precedence 80 for
@{'intersect $A $B}.
interpretation "intersect" 'intersect = intersect.

axiom ax_intersect1: ∀A,B. ∀Z. (Z ∈ A ∩ B → Z ∈ A ∧ Z ∈ B).
axiom ax_intersect2: ∀A,B. ∀Z. (Z ∈ A ∧ Z ∈ B → Z ∈ A ∩ B).

notation "'ABSURDUM' A" non associative with precedence 89 for @{'absurdum $A}.
interpretation "ex_false" 'absurdum A = (False_ind ? A).

(* Da qui in avanti riempite i puntini e fate validar quello che scrivete
   a Matita usando le icone con le frecce. *)

(* Exercise 1 *)
theorem reflexivity_inclusion: ∀A. A ⊆ A.
 assume A:set (* Ora dobbiamo dimostrare A ⊆ A, guarda il goal in alto a destra, è cambiato! *)
 we need to prove (∀Z. Z ∈ A → Z ∈ A) (ZA_to_ZA) (* da ora stiamo provando 'ZA_to_ZA' (guarda in alto a destra (Matita ha aggiunto un altra finestrella di dimostrazione), fino al relativo 'done' *)
  assume Z:(*BEGIN*)set(*END*)
  suppose (Z ∈ A) (ZA)
  by ZA done
  (* fine della prova di 'ZA_to_ZA' (guarda in alto a destra, Matita ha chiuso la finestrella di dimostrazione che aveva aperto),
     ora l'abbiamo guadagnata tra le ipotesi (ora compare nella lista in alto a destra)!
   Continuiamo con la prova del nostro teorema *)
 by ax_inclusion2, (*BEGIN*) ZA_to_ZA (*END*) done (* Quale ipotesi devo combinare con l'assioma? *)
qed.


(* Exercize 2 *)
theorem empty_absurd: ∀X, A. X ∈ ∅ → X ∈ A.
 assume X:set
 assume (*BEGIN*) A (*END*): set
 suppose (*BEGIN*)(X∈∅)(*END*) (X_in_empty)
 by ax_empty, (*BEGIN*)X_in_empty(*END*) we proved False (contraddizione) (* Andate a guardare cosa dice l'assioma ax_empty *)
 using (ABSURDUM contraddizione) done
qed.

(* Exercise 3 *)
theorem intersection_idempotent: ∀A. A ∩ A = A.
 assume A: (*BEGIN*)set(*END*) (* Da ora stiamo provando A ∩ A = A *)
 we need to prove (∀Z. Z ∈ A ∩ A ⇔ Z ∈ A) (main) (* da ora stiamo provando 'main' (Matita ha aperto una nuova finestrella di dimostrazione), fino al relativo 'done' *)
  assume (*BEGIN*)Z(*END*): set (* Ora dobbiamo dimostrare Z ∈ A ∩ A ⇔ Z ∈ A, guarda il goal in alto a destra *)
  (* Dimostriamo le due implicazioni:
     Da destra a sinistra: *)
  we need to prove (Z∈A→Z∈A∩A) (right_to_left) (* da ora stiamo provando 'right_to_left' (nuova finestrella), fino al relativo 'done' *)
    suppose (*BEGIN*)(Z ∈ A)(*END*)(ZA)
    by conj, (*BEGIN*)ZA(*END*) we proved (Z ∈ A ∧ Z ∈ A) (ZA_and_ZA)
    by ax_intersect2, (*BEGIN*)ZA_and_ZA(*END*) done (* Andate a guardare cosa dice l'assioma 'ax_intersect2' *)
  (* fine della prova di 'right_to_left' (Matita ha chiuso la finestrella di prima),
     ora l'abbiamo guadagnata tra le ipotesi (ora compare nella lista in alto a destra)!
   Continuiamo con la prova di 'main' *)
  (* Da sinistra a destra: *)
  we need to prove (*BEGIN*)(Z ∈ A ∩ A → Z ∈ A)(*END*) (left_to_right) (* da ora stiamo provando 'left_to_right' (nuova finestrella), fino al relativo 'done' *)
   suppose (*BEGIN*)(Z ∈ A ∩ A )(*END*) (Z_A_inters_A)
   by ax_intersect1, Z_A_inters_A we have (Z ∈ A) (ZA1) and (Z ∈ A) (ZA2)
   by (*BEGIN*)ZA1(*END*) done
   (* fine della prova di 'left_to_right',
      ora l'abbiamo guadagnata tra le ipotesi!
   Continuiamo con la prova di 'main' *)
  by (*BEGIN*)conj(*END*), left_to_right, right_to_left done
  (* fine della prova di 'main',
      ora l'abbiamo guadagnata tra le ipotesi (guarda la lista)!
  Continuiamo con la prova del nostro teorema *)
 by (*BEGIN*)ax_extensionality(*END*), main done
qed.

(* Exercise 4 *)
theorem intersect_empty: ∀A. A ∩ ∅ = ∅.
 assume (*BEGIN*)A: set(*END*)
 we need to prove (∀Z. Z∈A∩∅⇔Z∈∅) (II)
   assume (*BEGIN*)Z: set (*END*)
   we need to prove (Z∈A∩∅ → Z ∈∅) (I1)
     suppose (*BEGIN*)(Z∈A∩∅)(*END*) (Ze)
     by Ze, (*BEGIN*)ax_intersect1(*END*) we have (Z ∈ A) (ZA) and (Z∈∅) (ZE)
     by ZE done
   we need to prove (*BEGIN*)(Z∈∅→Z∈A∩∅)(*END*) (I2)
     suppose (*BEGIN*)(Z∈∅)(*END*) (ZE)
     by ZE, ax_empty we proved (*BEGIN*)False(*END*) (contraddizione)
     using (ABSURDUM (*BEGIN*)contraddizione(*END*)) done
   by (*BEGIN*)I1,I2,conj(*END*) done
 by II, (*BEGIN*)ax_extensionality(*END*)
done
qed.

(* Exercise 5 *)
theorem transitivity_inclusion: ∀A,B,C. A ⊆ B → B ⊆ C → A ⊆ C.
 assume (*BEGIN*)A:set(*END*)
 (*BEGIN*)assume(*END*) B:set
 (*BEGIN*)assume C:set(*END*)
 suppose (A ⊆ B) (AB)
 suppose (*BEGIN*)(B ⊆ C)(*END*) (BC)
 we need to prove (∀Z. Z ∈ A → Z ∈ C) (ZAtoZC)
  (*BEGIN*)assume Z:set(*END*)
  suppose (*BEGIN*)(Z ∈ A)(*END*) (ZA)
  by AB, ax_inclusion1, ZA we proved (*BEGIN*)(Z ∈ B)(*END*) (ZB)
  by (*BEGIN*)BC, ax_inclusion1, ZB(*END*) done (* Cosa dovete dimostrare (guardate il goal)? Che ipotesi avete a disposizione? *)
 by  ax_inclusion2, (*BEGIN*)ZAtoZC(*END*) done
qed.

(* Exercise 6 *)
theorem antisymmetry_inclusion: ∀A,B. A ⊆ B → B ⊆ A → A = B.
 (*BEGIN*)assume A: set(*END*)
 assume B: set
 suppose (*BEGIN*)(A ⊆ B)(*END*) (AB)
 suppose (B ⊆ A) (BA)
 we need to prove (∀Z. Z ∈ A ⇔ Z ∈ B) (P)
  (*BEGIN*)assume Z: set(*END*)
  by AB, ax_inclusion1 we proved (*BEGIN*)(Z ∈ A → Z ∈ B)(*END*) (AB')
  by (*BEGIN*)BA, ax_inclusion1(*END*)  we proved (Z ∈ B → Z ∈ A) (BA')
  by (*BEGIN*)conj, AB', BA'(*END*) done
 by P, (*BEGIN*)ax_extensionality(*END*) done (* Quale assioma devo utilizzare? *)
qed.

(* Exercise 7 *)
theorem intersect_commutative: ∀A,B. A ∩ B = B ∩ A.
 (*BEGIN*)assume A: set(*END*)
 (*BEGIN*)assume B: set(*END*)
 we need to prove (∀Z. Z ∈ A ∩ B ⇔ Z ∈ B ∩ A) (II)
   (*BEGIN*)assume Z: set(*END*)
   (* Facciamo prima l'implicazione da sinistra a destra: *)
   we need to prove (*BEGIN*)(Z∈A∩B→Z∈B∩A)(*END*) (I1)
     suppose (*BEGIN*)(Z∈A∩B)(*END*) (ZAB)
     we need to prove (Z ∈ B ∩ A)
      by ax_intersect1,ZAB we have (Z ∈ A) (ZA) and (*BEGIN*)(Z ∈ B)(*END*) (ZB)
      by (*BEGIN*)conj,ZB,ZA(*END*),ax_intersect2 done
      (* Ora che abbiamo finito l'implicazione =>, cosa manca da fare? Guarda il goal *)
   we need to prove (*BEGIN*)(Z∈B∩A → Z∈A∩B)(*END*) (I2)
     suppose (*BEGIN*)(Z∈B∩A)(*END*) (ZBA)
     we need to prove (*BEGIN*)(Z∈A∩B)(*END*)
     by (*BEGIN*)ax_intersect1,ZBA(*END*) we have (Z ∈ B) (ZB) and (Z∈A) (ZA)
     by ZA, ZB, (*BEGIN*)ax_intersect2,conj(*END*) done
   by (*BEGIN*)conj(*END*),I1,I2 done
 by (*BEGIN*)ax_extensionality,II(*END*) done
qed.
-/
