import LinearizabilityTheory.Interval
import Mathlib

namespace LinearizabilityTheory
open List
open Itv

structure Value where
  add : CItv
  rmv : CItv
  wf : add.b < rmv.a
  deriving DecidableEq, Repr

namespace Value

def beq : Value -> Value -> Bool
  | ⟨a1, r1, _⟩, ⟨a2, r2, _⟩ => a1 == a2 && r1 == r2

def timestamps (V : Value) : List Int :=
  [V.add.a, V.add.b, V.rmv.a, V.rmv.b]

abbrev disj_timestamps (v1 v2 : Value) : Prop :=
  v1.timestamps ∩ v2.timestamps = []

def cover (V : Value) : OItv :=
  ⟨V.add.b, V.rmv.a, V.wf⟩

theorem before_compat_trans_self {v1 : Value} {i : CItv}
  (vi : v1.rmv≼i) : v1.add ≼ i := by
  simp[Itv.before_compat] at *
  apply Int.le_of_lt
  calc
    _ < v1.add.b := v1.add.ab
    _ < v1.rmv.a := v1.wf
    _ ≤ i.b := vi

@[simp] theorem disj_timestamps_symm :
  Symmetric disj_timestamps := by
  intro v1 v2
  simp[disj_timestamps, timestamps, List.inter_eq_nil_iff_disjoint]
  grind

@[simp] theorem disj_timestamps_irrefl (v : Value) :
  ¬ disj_timestamps v v := by
  simp[disj_timestamps, timestamps]

@[simp] theorem disj_timestamps_xaa_yaa {x y : Value} :
  disj_timestamps x y -> x.add.a ≠ y.add.a := by
  intro hne eq; simp[disj_timestamps, timestamps] at hne; grind

@[simp] theorem disj_timestamps_xaa_yab {x y : Value} :
  disj_timestamps x y -> x.add.a ≠ y.add.b := by
  intro hne eq; simp[disj_timestamps, timestamps] at hne; grind

@[simp] theorem disj_timestamps_xaa_yra {x y : Value} :
  disj_timestamps x y -> x.add.a ≠ y.rmv.a := by
  intro hne eq; simp[disj_timestamps, timestamps] at hne; grind

@[simp] theorem disj_timestamps_xaa_yrb {x y : Value} :
  disj_timestamps x y -> x.add.a ≠ y.rmv.b := by
  intro hne eq; simp[disj_timestamps, timestamps] at hne; grind

@[simp] theorem disj_timestamps_xab_yaa {x y : Value} :
  disj_timestamps x y -> x.add.b ≠ y.add.a := by
  intro hne eq; simp[disj_timestamps, timestamps] at hne; grind

@[simp] theorem disj_timestamps_xab_yab {x y : Value} :
  disj_timestamps x y -> x.add.b ≠ y.add.b := by
  intro hne eq; simp[disj_timestamps, timestamps] at hne; grind

@[simp] theorem disj_timestamps_xab_yra {x y : Value} :
  disj_timestamps x y -> x.add.b ≠ y.rmv.a := by
  intro hne eq; simp[disj_timestamps, timestamps] at hne; grind

@[simp] theorem disj_timestamps_xab_yrb {x y : Value} :
  disj_timestamps x y -> x.add.b ≠ y.rmv.b := by
  intro hne eq; simp[disj_timestamps, timestamps] at hne; grind

@[simp] theorem disj_timestamps_xra_yaa {x y : Value} :
  disj_timestamps x y -> x.rmv.a ≠ y.add.a := by
  intro hne eq; simp[disj_timestamps, timestamps] at hne; grind

@[simp] theorem disj_timestamps_xra_yab {x y : Value} :
  disj_timestamps x y -> x.rmv.a ≠ y.add.b := by
  intro hne eq; simp[disj_timestamps, timestamps] at hne; grind

@[simp] theorem disj_timestamps_xra_yra {x y : Value} :
  disj_timestamps x y -> x.rmv.a ≠ y.rmv.a := by
  intro hne eq; simp[disj_timestamps, timestamps] at hne; grind

@[simp] theorem disj_timestamps_xra_yrb {x y : Value} :
  disj_timestamps x y -> x.rmv.a ≠ y.rmv.b := by
  intro hne eq; simp[disj_timestamps, timestamps] at hne; grind

@[simp] theorem disj_timestamps_xrb_yaa {x y : Value} :
  disj_timestamps x y -> x.rmv.b ≠ y.add.a := by
  intro hne eq; simp[disj_timestamps, timestamps] at hne; grind

@[simp] theorem disj_timestamps_xrb_yab {x y : Value} :
  disj_timestamps x y -> x.rmv.b ≠ y.add.b := by
  intro hne eq; simp[disj_timestamps, timestamps] at hne; grind

@[simp] theorem disj_timestamps_xrb_yra {x y : Value} :
  disj_timestamps x y -> x.rmv.b ≠ y.rmv.a := by
  intro hne eq; simp[disj_timestamps, timestamps] at hne; grind

@[simp] theorem disj_timestamps_xrb_yrb {x y : Value} :
  disj_timestamps x y -> x.rmv.b ≠ y.rmv.b := by
  intro hne eq; simp[disj_timestamps, timestamps] at hne; grind

theorem ne_of_disj_timestamps {v1 v2 : Value} :
  disj_timestamps v1 v2 -> v1 ≠ v2 := by
  intro h heq; subst heq; exact disj_timestamps_irrefl _ h



@[simp]
abbrev bot_of (v x : Value) : Prop :=
  (x.add.b < v.add.a -> x.rmv.a < v.add.b) ∧
  (x.add.b < v.rmv.a -> x.rmv.a < v.rmv.b)

@[simp]
abbrev left_of (x v : Value) : Prop :=
  x.rmv.a < v.add.b

@[simp]
abbrev right_of (x v : Value) : Prop :=
  v.rmv.a < x.add.b


@[simp]
theorem add_a_lt_rmv_b {v : Value} :
  v.add.a < v.rmv.b := by
  calc
    _ < v.add.b := v.add.ab
    _ < v.rmv.a := v.wf
    _ < v.rmv.b := v.rmv.ab


end Value
end LinearizabilityTheory
