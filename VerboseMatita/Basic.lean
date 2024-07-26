import Lean -- To allow Ctrl+Click over Lean syntax
import Verbose.English.All

open Lean
open Lean.Elab.Tactic

namespace matita

-- Bugs:
--  assume/suppose fanno anche change per via di Verbose
--  "it suffices to prove" (because of Verbose)
--  by ... not very strong
--  case is bugged

-- Todo:
--  eliminazione and/exists/iff
--  eliminazione dell'assurdo (sembra andare done?)
--  suppose ... that is equivalent to
--  case tactics that makes the hypothesis explicit

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
--  we proceed by cases on
--  case
--  by it suffice to prove
--  we split the proof

-- Debugging:
--  logInfo          chiamata
--  trace            tattica
--  Lean.addRawTrace

-- Tactics example:
-- elab_rules : tactic
-- |`(tactic| then) =>
--   withMainContext do
--    let x := (← getMainDecl).lctx.lastDecl.map (fun x ↦ x.toExpr)
--    Lean.addRawTrace x -/


syntax "assume " ident " : " term : tactic

macro_rules
  | `(tactic| assume $ident : $type) => `(tactic| Fix₁ $ident:ident : $type)

syntax "suppose " term (" as " ident)? : tactic

macro_rules
  | `(tactic| suppose $term as $ident) => `(tactic| Assume₁ $ident:ident : $term)
  | `(tactic| suppose $term) => `(tactic| intro)


syntax "_last_hypothesis_" : term

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

syntax (matitaJust)? " we " " proved " term ("as " ident)? : tactic
syntax (matitaJust)? " we " " proved " term "as " ident "and " term "as " ident : tactic
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
  | `(tactic | thus by $id we proved $term₁ as $ident₁ and $term₂ as $ident₂) =>
    `(tactic | thus by $id we proved $term₁ ∧ $term₂ <;> cases _last_hypothesis_ <;> case _ $ident₁:ident $ident₂:ident)

declare_syntax_cat matitaEquivalent

syntax "that " "is " "equivalent " "to " term : matitaEquivalent

syntax "we " "need " "to " "prove " term (matitaEquivalent)? : tactic

macro_rules
 | `(tactic | we need to prove $term) =>
  `(tactic | guard_target =ₛ $term)
 | `(tactic | we need to prove $exp that is equivalent to $inf) =>
  `(tactic | guard_target =ₛ $exp <;> change $inf)

macro "we " "split " "the " "proof " : tactic => `(tactic| first | apply And.intro | apply Iff.intro)

macro "we " "claim " stmt:term "as " name:ident "by" colGt prf:tacticSeq : tactic => `(tactic|have $name : $stmt := by $prf)
macro "we " "claim " stmt:term                  "by" colGt prf:tacticSeq : tactic => `(tactic|have _ : $stmt := by $prf)

macro "we " "proceed " "by " "cases " "on " name:ident "to " "prove " stmt:term : tactic => `(tactic|guard_target =ₛ $stmt <;> cases $name:term)

syntax "by " term "it suffices to prove " term : tactic -- "it suffices to prove " is a keyword in Verbose

elab_rules : tactic
 | `(tactic| by $term:term it suffices to prove $arg) => bySufficesTac term #[arg]

end matita

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

-- Union ∪
axiom union: set → set → set
infix:70 (priority := high) " ∪ " => union
axiom ax_union1: ∀A B, ∀Z, (Z ∈ A ∪ B → Z ∈ A ∨ Z ∈ B)
axiom ax_union2: ∀A B, ∀Z, (Z ∈ A ∨ Z ∈ B → Z ∈ A ∪ B)

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
 by ax_extensionality it suffices to prove ∀Z, Z ∈ A ∩ A ↔ Z ∈ A
 assume Z : set
 we split the proof
 . we need to prove Z ∈ A ∩ A → Z ∈ A
   suppose Z ∈ A ∩ A
   thus by ax_intersect1 we proved Z ∈ A as H₁ and Z ∈ A as H₂
   thus done
 . we need to prove Z ∈ A → Z ∈ A ∩ A
   suppose Z ∈ A
   thus by ax_intersect2 done

theorem union_symmetric: ∀A B, A ∪ B = B ∪ A := by
 assume A : set
 assume B : set
 by ax_extensionality it suffices to prove ∀Z, Z ∈ A ∪ B ↔ Z ∈ B ∪ A
 assume Z : set
 we split the proof
 . we need to prove Z ∈ A ∪ B → Z ∈ B ∪ A
   suppose Z ∈ A ∪ B
   thus by ax_union1 we proved Z ∈ A ∨ Z ∈ B as H
   we proceed by cases on H to prove Z ∈ B ∪ A
   . case a.mp.inl H
     thus by Or.inr we proved Z ∈ B ∨ Z ∈ A
     thus by ax_union2 done
   . case a.mp.inr H
     thus by Or.inr we proved Z ∈ B ∨ Z ∈ A
     thus by ax_union2 done
 . we need to prove Z ∈ B ∪ A → Z ∈ A ∪ B
   suppose Z ∈ B ∪ A
   thus by ax_union1 we proved Z ∈ B ∨ Z ∈ A as H
   we proceed by cases on H to prove Z ∈ A ∪ B
   . case a.mpr.inl H
     thus by Or.inr we proved Z ∈ A ∨ Z ∈ B
     thus by ax_union2 done
   . case a.mpr.inr H
     thus by Or.inr we proved Z ∈ A ∨ Z ∈ B
     thus by ax_union2 done

-- theorem intersect_empty: ∀A. A ∩ ∅ = ∅.
-- theorem transitivity_inclusion: ∀A,B,C. A ⊆ B → B ⊆ C → A ⊆ C.
-- theorem antisymmetry_inclusion: ∀A,B. A ⊆ B → B ⊆ A → A = B.
-- theorem intersect_commutative: ∀A,B. A ∩ B = B ∩ A.
--

end matita

section verbose
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

end verbose
