import LinearizabilityTheory.IntervalSet
import LinearizabilityTheory.AssocMap
import LinearizabilityTheory.Value
import Mathlib

namespace LinearizabilityTheory
open List
open Itv
open AssocMap

abbrev History := AssocMap Value Value.disj_timestamps

namespace History
open AssocMap Itv ItvSet Value

-- Equality helper
@[local simp]
def eq_iff {H1 H2 : History} :
    H1 = H2 ↔ ⸨H1⸩ = ⸨H2⸩ := by
  constructor
  · intro h; subst h; rfl
  · intro h
    obtain ⟨h1, _⟩ := H1
    obtain ⟨h2, _⟩ := H2
    simp; subst h; congr

-- Basic filters/removals
def rmv (H : History) (v : Value) : History :=
  H.filterV (fun o => o ≠ v)

def rmv_val (H : History) (n : Nat) : History :=
  H.filterK (fun v => v ≠ n)

def hist_minus (H : History) (R : History) : History :=
  H.filterK (fun k => k ∉ R.keys)

instance instSubHistory : Sub History where
  sub H1 H2 := H1.hist_minus H2

@[local simp] theorem hist_sub_def (H : History) (R : History) :
  H - R = H.hist_minus R := rfl

def hist_minus_vals (H : History) (R : List Nat) : History :=
  H.filterK (fun k => k ∉ R)

instance instHSubHistoryListNat : HSub History (List Nat) History where
  hSub H1 H2 := H1.hist_minus_vals H2

@[local simp] theorem hist_hsub_def (H : History) (R : History) :
  H - R = H.hist_minus R := rfl

@[simp] theorem hsub_nil (H : History) :
  (H - ([] : List Nat)) = H := by
  unfold HSub.hSub instHSubHistoryListNat
  simp[hist_minus_vals, AssocMap.filterK, AssocMap.filter]

@[simp] theorem sub_empty (H : History) :
  (H - (∅ : History)) = H := by
  rw[hist_sub_def]
  simp[hist_minus, filterK, AssocMap.filter]

-- Minimal/maximal projections and membership lemmas
def minimal (H : History) : History :=
  H.filterV (fun v => ∀ w ∈ H, v.add.a ≤ w.2.add.b)

theorem mem_minimal_iff {H : History} {v} :
  v ∈ H.minimal ↔ v ∈ H ∧ (∀ w ∈ H, v.2.add.a ≤ w.2.add.b) := by
  simp[minimal, AssocMap.filterV, AssocMap.mem_filter]

def maximal (H : History) : History :=
  H.filterV (fun v => ∀ w ∈ H, w.2.rmv.a ≤ v.rmv.b)

theorem mem_maximal_iff {H : History} {v} :
  v ∈ H.maximal ↔ v ∈ H ∧ (∀ w ∈ H, w.2.rmv.a ≤ v.2.rmv.b) := by
  simp[maximal, AssocMap.filterV, AssocMap.mem_filter]

theorem mem_ne_key_ne_val {H : History} {a b : Nat × Value} :
  a ∈ H -> b ∈ H -> a.1 ≠ b.1 -> a.2 ≠ b.2 := by
  intro ha hb hne
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  have := hne.symm
  simp at hne
  apply Value.ne_of_disj_timestamps
  apply pred_ok _ _ _ ha hb hne


def populated (H : History) : ItvSet false :=
  ItvSet.fromList
    (H.inner.map (·.2.cover))

theorem mem_ex_populated {H : History} {q} :
  q ∈ H -> ∃ q' ∈ H.populated, q'.a ≤ q.2.add.b ∧ q.2.rmv.a ≤ q'.b := by
  intro qH
  simp[History.populated]
  obtain ⟨H, Hv, Ho⟩ := H
  simp[AssocMap.mem_iff] at *
  induction H with
  | nil => simp at *
  | cons a as ih =>
      simp[ItvSet.fromList_cons] at *
      cases qH with
      | inl h1 =>
          subst h1
          apply ItvSet.add_contained_new
      | inr h2 =>
          let vq := a.2.cover
          let ⟨q', q'H, q'l, q'r⟩ := ih Hv.2 (pred_skip Ho) h2
          obtain ⟨q'', q''H, q''l, q''r⟩ := ItvSet.add_contained_old _ _ q'H vq
          subst vq
          use q''
          apply And.intro
          · exact q''H
          · grind


theorem uniq_ts (H : History) (ts : Int) :
  ∀ x y, x ∈ H -> y ∈ H -> ts ∈ x.2.timestamps -> ts ∈ y.2.timestamps -> x = y := by
  intro ⟨x1,x2⟩ ⟨y1, y2⟩ xH yH xts yts
  by_cases xy: x1 = y1
  case pos =>
      simp[xy] at xH ⊢
      exact AssocMap.mem_inj _ xH yH
  case neg =>
  let okp := H.pred_ok ⟨x1, x2⟩ ⟨y1, y2⟩ xH yH xy
  simp[Value.disj_timestamps, Value.timestamps] at okp xts yts
  simp[List.inter_eq_nil_iff_disjoint] at okp
  grind

theorem populated_lb (H : History) :
  ∀ i ∈ H.populated, ∃ a b, (a, b) ∈ H ∧ i.a = b.add.b := by
  intro itv iH
  simp[History.populated] at iH
  obtain ⟨H, Hv, Ho⟩ := H
  induction H generalizing itv with
  | nil => simp at iH; contradiction
  | cons v vs ih =>
      simp[ItvSet.fromList_cons] at iH ih
      let Q := ItvSet.add_mem_lb _ _ _ iH
      cases Q with
      | inl H1 =>
          use v.1, v.2
          simp[H1, Value.cover]
      | inr H2 =>
          obtain ⟨q1, qH, qE⟩ := H2
          let ⟨a, b, abH, eq⟩ := ih q1 (wf_skip Hv) (pred_skip Ho) qH
          simp[qE, AssocMap.mem_iff] at abH ⊢
          use a, b
          simp[eq, abH]

theorem populated_ub (H : History) :
  ∀ i ∈ H.populated, ∃ a b, (a, b) ∈ H ∧ i.b = b.rmv.a := by
  intro itv iH
  simp[History.populated] at iH
  obtain ⟨H, Hv, Ho⟩ := H
  induction H generalizing itv with
  | nil => simp at iH; contradiction
  | cons v vs ih =>
      simp[ItvSet.fromList_cons] at iH ih
      let Q := ItvSet.add_mem_ub _ _ _ iH
      cases Q with
      | inl H1 =>
          use v.1, v.2
          simp[H1, Value.cover]
      | inr H2 =>
          obtain ⟨q1, qH, qE⟩ := H2
          let ⟨a, b, abH, eq⟩ := ih q1 (wf_skip Hv) (pred_skip Ho) qH
          simp[qE, AssocMap.mem_iff] at abH ⊢
          use a, b
          simp[eq, abH]



abbrev deserted (H : History) : ItvSet true :=
  H.populated.complement




theorem deserted_sound (H : History) :
      ∀ q ∈ H,
        ∀ itv ∈ H.deserted,
          q.2.add.b < itv.b -> q.2.rmv.a < itv.b := by
    -- Proof outline:
    -- Otherwise, the populated of q would intersect itv, contradiction.
    intro q qH i iO qab_ib
    -- Get the populated interval that populateds q
    obtain ⟨qc, qcC, qcl, qcr⟩ := History.mem_ex_populated qH
    let Q := ItvSet.complement_disjoint H.populated qcC iO
    simp at Q
    let Q' := ItvSet.left_complement qcC i iO
    have qcib : qc.a < i.b := by grind
    let Q' := Q' qcib
    calc
      _ ≤ _ := qcr
      _ ≤ _ := Q'
      _ < _ := i.ab

def separated_by {H : History} (ts : Int) : Prop :=
  (∀ x ∈ H, x.2.rmv.a ≤ ts ∨ ts ≤ x.2.add.b) ∧ -- all are somewhere
  (∃ x ∈ H, x.2.rmv.a ≤ ts) ∧ -- at least one in L
  (∃ x ∈ H, ts ≤ x.2.add.b) -- at least one in R

theorem sep_by_deserted (H : History) :
    ∀ itv ∈ H.deserted.val,
      H.separated_by itv.b := by
  intro itv iH
  simp[separated_by]
  apply And.intro
  · intro a b abH
    let Q := History.deserted_sound H (a, b) abH itv iH
    simp at Q
    by_cases h: b.add.b < itv.b
    case pos => simp[Int.le_of_lt (Q h)]
    case neg =>
      simp at h
      simp[h]
  · apply And.intro
    · let ⟨z, zC, zE⟩ := ItvSet.complement_mem_lb H.populated itv iH
      let ⟨a, b, abH, abE⟩ := History.populated_ub H z zC
      use a, b
      simp[abH, ← abE, ← zE, Int.le_of_lt itv.ab]
    · let ⟨z, zC, zE⟩ := ItvSet.complement_mem_ub H.populated itv iH
      let ⟨a, b, abH, abE⟩ := History.populated_lb H z zC
      use a, b
      simp[abH, abE, zE]


theorem rmv_val_smaller {H : History} {t : Nat} :
  t ∈ H.keys ->
    (H.rmv_val t).inner.length < H.inner.length := by
    intro tK
    obtain ⟨H, Hv, Ho⟩ := H
    induction H with
    | nil => simp at tK
    | cons a as ih =>
        simp[rmv_val, AssocMap.filterK, List.filter_cons, AssocMap.keys] at ih tK ⊢
        by_cases ta : a.1 = t
        case pos =>
            simp[ta]
            grind
        case neg =>
            have ta' : t ≠ a.1 := by grind
            simp[ta, ta'] at tK ⊢
            exact tK

theorem deserted_of_two_populated {H : History} {l r} :
  l ∈ H.populated -> r ∈ H.populated ->
    l.b ≤ r.a -> H.deserted ≠ ∅ := by
  intro lH rH labra
  simp[History.deserted]
  rw[ItvSet.complement_empty_iff]
  have l_ne_r : l ≠ r := by
    obtain ⟨l1, l2, _⟩ := l
    obtain ⟨r1, r2, r12⟩ := r
    simp at *
    intro eq1 eq2
    simp[eq2] at labra
    exact labra.not_gt r12
  let Q := List.length_ge_two_of_two_diff lH rH l_ne_r
  simp[Q]




theorem mem_xs_ne_timestamps {x : Nat × Value} {xs : List (Nat × Value)}
  {y : Itv false}
  (wf : wf_map (x :: xs)) (pok : val_pred (x :: xs) Value.disj_timestamps)
  (ym : y ∈ History.populated ⟨xs, wf_skip wf, val_pred_skip pok⟩)
  : y.b ≠ x.2.cover.a ∧ y.a ≠ x.2.cover.b := by
    let L := populated_lb ⟨xs, wf_skip wf, val_pred_skip pok⟩ y ym
    let R := populated_ub ⟨xs, wf_skip wf, val_pred_skip pok⟩ y ym
    simp[AssocMap.mem_iff] at L R
    obtain ⟨l, lv, lH, lE⟩ := L
    obtain ⟨r, rv, rH, rE⟩ := R
    let ll := (wf_head wf) (l, lv) lH
    let rl := (wf_head wf) (r, rv) rH
    simp at ll rl

    let Q := (val_pred_head pok) (l, lv) lH ll.ne
    let P := (val_pred_head pok) (r, rv) rH rl.ne
    let Q := Value.disj_timestamps_symm Q
    let P := Value.disj_timestamps_symm P

    have yrx : y.b ≠ x.2.add.b := by
      simp[rE]
      simp[Value.disj_timestamps, List.inter_eq_nil_iff_disjoint, List.disjoint_iff_ne] at P
      apply P <;> simp[Value.timestamps]

    have yax : y.a ≠ x.2.rmv.a := by
      simp[lE]
      simp[Value.disj_timestamps, List.inter_eq_nil_iff_disjoint, List.disjoint_iff_ne] at Q
      apply Q <;> simp[Value.timestamps]

    simp[Value.cover, yax, yrx]


theorem mem_pop_mem_cover {H : History} {ts : Int} :
  H.populated.contains ts -> ∃ x ∈ H, ts ∈ x.2.cover := by
  simp[ItvSet.contains]
  obtain ⟨H, Hv, Ho⟩ := H

  induction H with
  | nil => simp[populated, ItvSet.fromList]
  | cons x xs ih =>
      simp[← ItvSet.mem_iff]
      intro j iaH tsj
      let Q := ItvSet.mem_add iaH
      cases Q with
      | inl Q1 =>
          obtain ⟨ql, qr⟩ := Q1
          subst ql
          simp[Itv.instMembershipInt] at tsj
          use x.1, x.2
          simp
          exact tsj
      | inr Q =>
        cases Q with
        | inl Q2 =>
            obtain ⟨y, yH, ytj⟩ := Q2
            let ⟨a, b, jL, jR⟩ := ih (wf_skip Hv) (pred_skip Ho) j y tsj
            use a, b
            simp[AssocMap.mem_iff] at jL
            simp[AssocMap.mem_iff, jL, jR]
        | inr Q =>
          cases Q with
          | inl Q3 =>
              obtain ⟨jm, nytj⟩ := Q3
              let ⟨a, b, jL, jR⟩ := ih (wf_skip Hv) (pred_skip Ho) j jm tsj
              use a, b
              simp[AssocMap.mem_iff] at jL
              simp[AssocMap.mem_iff, jL, jR]
          | inr Q =>
            cases Q with
            | inl Q4 =>
                obtain ⟨y, ym, nytj, jE⟩ := Q4
                simp[jE, Itv.instMembershipInt] at tsj



                have y_o_x : y.overlaps x.2.cover := by
                  let ⟨yrx, yax⟩ := History.mem_xs_ne_timestamps Hv Ho ym
                  unfold Value.cover at yrx yax
                  simp[Itv.overlaps, Value.cover] at ⊢
                  simp[Itv.touches, Int.le_iff_lt_or_eq, Value.cover, yax, yrx.symm] at nytj
                  simp[nytj]


                let Q := Itv.union_contains y_o_x |>.mp tsj
                cases Q with
                | inl yH =>
                  let ⟨a, b, jL, jR⟩ := ih (wf_skip Hv) (pred_skip Ho) y ym yH
                  use a, b
                  simp[AssocMap.mem_iff] at jL
                  simp[AssocMap.mem_iff, jL, jR]
                | inr xts =>
                  use x.1, x.2
                  simp
                  exact xts
            | inr Q5 =>
                obtain ⟨l, r, lm, rm, lr, ltx, rtx, jE⟩ := Q5
                simp[jE] at tsj
                have rxtr : (l.union x.2.cover).overlaps r := by
                  let ⟨rrx, rax⟩ := History.mem_xs_ne_timestamps Hv Ho rm
                  unfold Value.cover at rrx rax
                  simp[
                    Itv.union, Itv.touches, Value.cover, Itv.overlaps,
                    Int.le_iff_lt_or_eq, rax, rrx.symm
                    ] at rtx ⊢
                  simp[rtx]
                let Q := Itv.union_contains rxtr |>.mp tsj
                cases Q with
                | inl lH =>
                  have ltx' : l.overlaps x.2.cover := by
                    let ⟨lrx, lax⟩ := History.mem_xs_ne_timestamps Hv Ho lm
                    unfold Value.cover at lrx lax
                    simp[
                      Itv.touches, Value.cover, Itv.overlaps,
                      Int.le_iff_lt_or_eq, lax, lrx.symm
                      ] at ltx ⊢
                    simp[ltx]

                  let Q := Itv.union_contains ltx' |>.mp lH
                  cases Q with
                  | inl lH =>
                    let ⟨a, b, abm, tb⟩ := ih (wf_skip Hv) (pred_skip Ho) l lm lH
                    use a,b
                    simp[AssocMap.mem_iff] at abm
                    simp[AssocMap.mem_iff, abm, tb]
                  | inr xts =>
                    use x.1, x.2
                    simp
                    exact xts
                | inr rH =>
                  let ⟨a, b, abm, tb⟩ := ih (wf_skip Hv) (pred_skip Ho) r rm rH
                  use a,b
                  simp[AssocMap.mem_iff] at abm
                  simp[AssocMap.mem_iff, abm, tb]



theorem mem_cover_not_sep {H : History} {ts : Int} :
  (∃ x ∈ H, ts ∈ x.2.cover) -> ¬ H.separated_by ts := by
  simp[History.separated_by]
  intro x1 x2 xH tsx all
  exfalso
  let Q := all x1 x2 xH
  simp[Itv.instMembershipInt, Value.cover, Itv.contains] at tsx
  simp[tsx.1.not_ge, tsx.2.not_ge] at Q


theorem mem_pop_nonsep_val {H : History} {ts : Int} :
  H.populated.contains ts -> ¬ H.separated_by ts := by
  intro pop
  let ⟨x, xH, tsxc⟩ := History.mem_pop_mem_cover pop
  exact History.mem_cover_not_sep (by use x)


theorem mem_populated_ne_ordered {H : History} {l r} :
  l ∈ H.populated -> r ∈ H.populated -> l ≠ r ->
  l.b < r.a ∨ r.b < l.a := List.pairwise_iff_Rab_or_Rba (H.populated.prop)

theorem separated_by_deserted_nonempty {H : History} {ts} :
  H.separated_by ts -> H.deserted ≠ ∅ := by
  intro sep
  let tmp := sep
  simp[History.separated_by] at sep
  obtain ⟨wf_sep, lmem, rmem⟩ := sep
  obtain ⟨l, lv, lvH, lts⟩ := lmem
  obtain ⟨r, rv, rvH, tsr⟩ := rmem

  obtain ⟨q, qC, qlt, ltq⟩ := History.mem_ex_populated lvH
  obtain ⟨s, sC, slt, stq⟩ := History.mem_ex_populated rvH

  by_cases qs : q = s
  case pos =>
    subst qs
    have tsm : H.populated.contains ts := by
      simp[ItvSet.contains]
      use q, qC
      simp at *
      simp[Itv.instMembershipInt, Itv.contains]
      have qts : q.a < ts := by calc
        _ ≤ lv.add.b := qlt
        _ < lv.rmv.a := lv.wf
        _ ≤ ts := lts
      have tsq : ts < q.b := by calc
        _ ≤ rv.add.b := tsr
        _ < rv.rmv.a := rv.wf
        _ ≤ _ := stq
      simp[qts, tsq]
    let nsep := (History.mem_pop_nonsep_val tsm) tmp
    contradiction
  case neg =>
    let Q := History.mem_populated_ne_ordered qC sC qs
    cases Q with
    | inl qlt =>
        exact deserted_of_two_populated qC sC qlt.le
    | inr slt =>
        exact deserted_of_two_populated sC qC slt.le


theorem getAt_empty_not_sep {H : History} {ts} :
  H.populated.getAt ts = [] -> ¬ H.separated_by ts := by
  intro hget sep
  simp[History.separated_by] at sep
  obtain ⟨wf_sep, lmem, rmem⟩ := sep
  obtain ⟨l, lv, lvH, lts⟩ := lmem
  obtain ⟨r, rv, rvH, tsr⟩ := rmem

  let Q := ItvSet.getAt_empty hget

  cases Q with
  | inl Q =>
      let ⟨a, b, abm, tb⟩ := History.mem_ex_populated rvH
      let J := Q a b
      simp[Itv.left_of] at J
      simp_all
      apply Int.lt_irrefl ts
      calc
        _ ≤ rv.add.b := tsr
        _ < rv.rmv.a := rv.wf
        _ ≤ _ := tb
        _ ≤ _ := J
  | inr Q =>
      let ⟨a, b, abm, tb⟩ := History.mem_ex_populated lvH
      let J := Q a b
      simp[Itv.right_of] at J
      simp_all
      apply Int.lt_irrefl ts
      calc
        _ ≤ a.a := J
        _ ≤ lv.add.b := abm
        _ < lv.rmv.a := lv.wf
        _ ≤ ts := lts


theorem separated_by_deserted_contains {H : History} {ts} :
  H.separated_by ts -> ∃ q ∈ H.deserted, q.contains ts := by
  intro sep
  let Q := ItvSet.getAt H.populated ts
  have QE : ItvSet.getAt H.populated ts = Q := rfl
  revert QE

  cases Q with
  | nil =>
      intro QE
      exfalso
      apply History.getAt_empty_not_sep QE sep
  | cons a rest =>
      intro QE
      cases rest with
      | nil =>
          let J := ItvSet.getAt_single QE
          let Q := History.mem_pop_nonsep_val (by use a, J.1; exact J.2) sep
          contradiction
      | cons b rest =>
          cases rest with
          | nil => exact ItvSet.getAt_two_complement QE
          | cons c rest => simp at QE


theorem separated_left_right {H : History} {ts} :
  H.separated_by ts ->
    ∃ l ∈ H.populated, ∃ r ∈ H.populated, l.b ≤ ts ∧ ts ≤ r.a := by
  intro sby
  let ⟨q, qM, qts⟩ := History.separated_by_deserted_contains sby
  let ⟨l, lm, lh⟩ := ItvSet.complement_mem_lb H.populated q qM
  let ⟨r, rm, rh⟩ := ItvSet.complement_mem_ub H.populated q qM
  use l, lm, r, rm
  simp[← lh, ← rh]
  exact qts


theorem deserted_empty_no_sep {H : History} :
  H.deserted = ∅ -> ∀ ts, ¬ H.separated_by ts := by
  intro de ts sby
  let ⟨q, qm, qh⟩ := History.separated_by_deserted_contains sby
  rw[ItvSet.eq_nil_if_forall_not_mem] at de
  have qnmem : q ∉ H.deserted := de q
  contradiction



end History
end LinearizabilityTheory
