import Mathlib

/-!
# Erdős Problem 548

*Reference:* [erdosproblems.com/548](https://www.erdosproblems.com/548)

## Proof outline

For each permutation word of the host vertices, distinguish its first vertex
as a root image. Count the prefixes of its remaining word which end at a
neighbor of that root image and support a rooted copy of the target tree.

Two reversible word operations provide the induction:
* Rotating the first qualifying prefix past the rest of a prefix gives the
  branch-gluing inequality (`marked_word_gluing_count`).
* Reversing both blocks at a cut moves the root to a newly attached leaf,
  losing at most one state per full word (`rooted_word_leaf_move_count`).

Splitting at a nonleaf root, or deleting a leaf root, then proves
`rooted_word_tree_bound`: the number of all adjacency-marked states is at most
the rooted-copy count plus `(t - 2) * n!` for a target of order `t ≥ 2`.
The marked-state count is exactly `2 * |E(G)| * (n - 1)!`. If the target is
absent, cancellation yields `2 * |E(G)| ≤ (t - 2) * n`, contradicting the
stated density. All counts and injections below are finite and exact.
-/

open SimpleGraph

/- Reversible prefix-block rotation for finite marked-word counting.
No graph-density statement is assumed in this file. -/
namespace Erdos548

/-- A nonempty marked last letter. -/
def MarkedEnd {α : Type*} (N : α → Prop) (l : List α) : Prop :=
  ∃ a, l.getLast? = some a ∧ N a

lemma markedEnd_not_nil {α : Type*} {N : α → Prop} {l : List α}
    (h : MarkedEnd N l) : l ≠ [] := by
  rintro rfl
  obtain ⟨a,ha,_⟩ := h
  simp at ha

lemma markedEnd_append_right {α : Type*} {N : α → Prop} {r x : List α}
    (h : MarkedEnd N (r++x)) (hx : x ≠ []) : MarkedEnd N x := by
  obtain ⟨a,ha,hN⟩ := h
  have hn : x.getLast? ≠ none := fun he => hx (List.getLast?_eq_none_iff.mp he)
  cases he : x.getLast? with
  | none => exact (hn he).elim
  | some b =>
    rw [List.getLast?_append,he] at ha
    change some b = some a at ha
    have hba := Option.some.inj ha
    subst b
    exact ⟨a,he,hN⟩

/-- The displayed word is the first qualifying prefix of any extension. -/
def FirstPrefix {α : Type*} (P : List α → Prop) (r : List α) : Prop :=
  P r ∧ ∀ j < r.length, ¬P (r.take j)

lemma firstPrefix_unique {α : Type*} {P : List α → Prop} {r y r' y' : List α}
    (hr : FirstPrefix P r) (hr' : FirstPrefix P r') (he : r++y=r'++y') :
    r=r' ∧ y=y' := by
  have hlen : r.length=r'.length := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with h | h
    · have hh := congrArg (List.take r.length) he
      rw [List.take_left,List.take_append_of_le_length h.le] at hh
      exact hr'.2 r.length h (hh ▸ hr.1)
    · have hh := congrArg (List.take r'.length) he
      rw [List.take_append_of_le_length h.le,List.take_left] at hh
      exact hr.2 r'.length h (hh.symm ▸ hr'.1)
  exact ⟨List.append_inj_left he hlen,List.append_inj_right he hlen⟩

lemma firstPrefix_rotation_injective {α : Type*} {P : List α → Prop}
    {r x y r' x' y' : List α} (hr : FirstPrefix P r) (hr' : FirstPrefix P r')
    (he : (x++(r++y),x.length)=(x'++(r'++y'),x'.length)) :
    ((r++x)++y,r.length+x.length)=((r'++x')++y',r'.length+x'.length) := by
  have hword := congrArg Prod.fst he
  have hlen := congrArg Prod.snd he
  have hx : x=x' := List.append_inj_left hword hlen
  have hs : r++y=r'++y' := List.append_inj_right hword hlen
  obtain ⟨hrEq,hyEq⟩ := firstPrefix_unique hr hr' hs
  subst x'
  subst r'
  subst y'
  rfl

/-- Cut at the first qualifying marked prefix and rotate it past the rest of
an input prefix. Its new prefix is a disjoint difference and hence cannot
belong to the second family. -/
lemma marked_prefix_rotation_exists {α : Type*} [DecidableEq α]
    (N : α → Prop) (A B C : Finset α → Prop)
    (hglue : ∀ R X, Disjoint R X → A R → B X → C (R ∪ X))
    (l : List α) (hl : l.Nodup) (k : ℕ) (hk : k ≤ l.length)
    (hm : MarkedEnd N (l.take k)) (hA : A (l.take k).toFinset)
    (hC : ¬C (l.take k).toFinset) :
    ∃ r x y : List α,
      l=(r++x)++y ∧ k=r.length+x.length ∧
      FirstPrefix (fun q => MarkedEnd N q ∧ A q.toFinset ∧ ¬C q.toFinset) r ∧
      (x=[] ∨ MarkedEnd N x) ∧ ¬B x.toFinset := by
  classical
  let P : List α → Prop := fun q => MarkedEnd N q ∧ A q.toFinset ∧ ¬C q.toFinset
  have hex : ∃ j, j ≤ k ∧ P (l.take j) := ⟨k,le_rfl,hm,hA,hC⟩
  let j := Nat.find hex
  have hjk : j ≤ k := (Nat.find_spec hex).1
  have hjP : P (l.take j) := (Nat.find_spec hex).2
  let r := l.take j
  let x := (l.drop j).take (k-j)
  let y := l.drop k
  have hrlen : r.length=j := by simp only [r,List.length_take]; omega
  have hxlen : x.length=k-j := by
    simp only [x,List.length_take,List.length_drop]
    omega
  have hrx : r++x=l.take k := by
    dsimp only [r,x]
    rw [← List.take_add]
    congr 1
    omega
  have hword : (r++x)++y=l := by
    rw [hrx]
    exact List.take_append_drop k l
  refine ⟨r,x,y,hword.symm,by omega,⟨hjP,?_⟩,?_,?_⟩
  · intro i hi hPi
    have hij : i < j := by omega
    have hp : P (l.take i) := by
      simpa only [r,List.take_take,Nat.min_eq_left hij.le] using hPi
    exact Nat.find_min hex hij ⟨by omega,hp⟩
  · by_cases hx : x=[]
    · exact Or.inl hx
    · exact Or.inr (markedEnd_append_right (hrx.symm ▸ hm) hx)
  · intro hB
    have hnr : (r++x).Nodup := hrx.symm ▸ hl.sublist (List.take_sublist k l)
    have hd : Disjoint r.toFinset x.toFinset := by
      apply Finset.disjoint_left.mpr
      intro a ha hb
      exact (List.disjoint_left.mp hnr.disjoint) (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb)
    have hh := hglue r.toFinset x.toFinset hd hjP.2.1 hB
    apply hC
    rwa [← List.toFinset_append,hrx] at hh

/-- The relation records the reversible block rotation, without choosing a
particular implementation of the first-prefix search. -/
def PrefixRotation {α : Type*} (P : List α → Prop)
    (u v : List α × ℕ) : Prop :=
  ∃ r x y : List α, u=((r++x)++y,r.length+x.length) ∧
    v=(x++(r++y),x.length) ∧ FirstPrefix P r

lemma prefixRotation_left_unique {α : Type*} {P : List α → Prop}
    {u u' v : List α × ℕ} (h : PrefixRotation P u v) (h' : PrefixRotation P u' v) : u=u' := by
  obtain ⟨r,x,y,rfl,hv,hr⟩ := h
  obtain ⟨r',x',y',rfl,hv',hr'⟩ := h'
  exact firstPrefix_rotation_injective hr hr' (hv.symm.trans hv')

noncomputable def allowedWordCuts {α : Type*} (W : Finset (List α)) (m : ℕ)
    (N : α → Prop) : Finset (List α × ℕ) := by
  classical
  exact (W ×ˢ Finset.range (m+1)).filter (fun p => p.2=0 ∨ MarkedEnd N (p.1.take p.2))

noncomputable def goodWordCuts {α : Type*} [DecidableEq α]
    (W : Finset (List α)) (m : ℕ) (N : α → Prop) (A : Finset α → Prop) :
    Finset (List α × ℕ) := by
  classical
  exact (W ×ˢ Finset.range (m+1)).filter
    (fun p => MarkedEnd N (p.1.take p.2) ∧ A (p.1.take p.2).toFinset)

lemma goodWordCuts_subset_allowed {α : Type*} [DecidableEq α]
    (W : Finset (List α)) (m : ℕ) (N : α → Prop) (A : Finset α → Prop) :
    goodWordCuts W m N A ⊆ allowedWordCuts W m N := by
  classical
  intro p hp
  obtain ⟨hp,hm,_⟩ := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr ⟨hp,Or.inr hm⟩

lemma goodWordCuts_mono {α : Type*} [DecidableEq α]
    (W : Finset (List α)) (m : ℕ) (N : α → Prop) (A C : Finset α → Prop)
    (hCA : ∀ X, C X → A X) : goodWordCuts W m N C ⊆ goodWordCuts W m N A := by
  classical
  intro p hp
  obtain ⟨hp,hm,hC⟩ := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr ⟨hp,hm,hCA _ hC⟩

/-- The exact finite marked-word gluing inequality. The ambient word family
must be closed under permutation; every word is repetition-free. -/
lemma marked_word_gluing_count {α : Type*} [DecidableEq α]
    (W : Finset (List α)) (m : ℕ) (N : α → Prop) (A B C : Finset α → Prop)
    (hlen : ∀ l ∈ W, l.length=m) (hnodup : ∀ l ∈ W, l.Nodup)
    (hperm : ∀ l ∈ W, ∀ l', l'.Perm l → l' ∈ W)
    (hCA : ∀ X, C X → A X)
    (hglue : ∀ R X, Disjoint R X → A R → B X → C (R ∪ X)) :
    (goodWordCuts W m N A).card + (goodWordCuts W m N B).card ≤
      (allowedWordCuts W m N).card + (goodWordCuts W m N C).card := by
  classical
  let D := goodWordCuts W m N A \ goodWordCuts W m N C
  let E := allowedWordCuts W m N \ goodWordCuts W m N B
  let P : List α → Prop := fun q => MarkedEnd N q ∧ A q.toFinset ∧ ¬C q.toFinset
  have hex : ∀ u : ↥D, ∃ v : ↥E, PrefixRotation P u.val v.val := by
    rintro ⟨⟨l,k⟩,hu⟩
    obtain ⟨huA,huC⟩ := Finset.mem_sdiff.mp hu
    obtain ⟨hbase,hm,hA⟩ := Finset.mem_filter.mp huA
    obtain ⟨hlW,hkr⟩ := Finset.mem_product.mp hbase
    have hlm := hlen l hlW
    have hk : k ≤ l.length := by have := Finset.mem_range.mp hkr; omega
    have hC : ¬C (l.take k).toFinset := by
      intro hc
      exact huC (Finset.mem_filter.mpr ⟨hbase,hm,hc⟩)
    obtain ⟨r,x,y,hword,hcut,hr,hx,hBx⟩ :=
      marked_prefix_rotation_exists N A B C hglue l (hnodup l hlW) k hk hm hA hC
    let q := x++(r++y)
    have hqperm : q.Perm l := by
      rw [hword]
      simpa only [q,List.append_assoc] using
        (List.perm_append_comm (l₁:=x) (l₂:=r)).append_right y
    have hqW : q ∈ W := hperm l hlW q hqperm
    have hqLen : q.length=m := (List.Perm.length_eq hqperm).trans hlm
    have hxle : x.length ≤ m := by simp only [q,List.length_append] at hqLen; omega
    have htake : q.take x.length=x := List.take_left
    have hqBase : (q,x.length) ∈ W ×ˢ Finset.range (m+1) :=
      Finset.mem_product.mpr ⟨hqW,Finset.mem_range.mpr (by omega)⟩
    have hqAllowed : (q,x.length) ∈ allowedWordCuts W m N := by
      apply Finset.mem_filter.mpr
      refine ⟨hqBase,?_⟩
      rcases hx with hx | hx
      · exact Or.inl (hx ▸ rfl)
      · exact Or.inr (htake.symm ▸ hx)
    have hqNot : (q,x.length) ∉ goodWordCuts W m N B := by
      intro hh
      have hb := (Finset.mem_filter.mp hh).2.2
      rw [htake] at hb
      exact hBx hb
    refine ⟨⟨(q,x.length),Finset.mem_sdiff.mpr ⟨hqAllowed,hqNot⟩⟩,r,x,y,?_,rfl,hr⟩
    exact Prod.ext hword hcut
  choose f hf using hex
  have hi : Function.Injective f := by
    intro u u' he
    apply Subtype.ext
    apply prefixRotation_left_unique (hf u)
    rw [he]
    exact hf u'
  have hcard : D.card ≤ E.card := Finset.card_le_card_of_injective hi
  have hAC := Finset.card_sdiff_add_card_eq_card (goodWordCuts_mono W m N A C hCA)
  have hBE := Finset.card_sdiff_add_card_eq_card (goodWordCuts_subset_allowed W m N B)
  change (goodWordCuts W m N A \ goodWordCuts W m N C).card ≤
    (allowedWordCuts W m N \ goodWordCuts W m N B).card at hcard
  omega

end Erdos548

/- Exact cardinalities of permutation words and marked prefixes. -/
namespace Erdos548
attribute [local instance] Classical.propDecidable

noncomputable def permutationWords {α : Type*} [DecidableEq α] (l : List α) :
    Finset (List α) := l.permutations.toFinset

lemma mem_permutationWords {α : Type*} [DecidableEq α] (l q : List α) :
    q ∈ permutationWords l ↔ q.Perm l := by
  simp only [permutationWords,List.mem_toFinset,List.mem_permutations]

lemma permutationWords_card {α : Type*} [DecidableEq α] (l : List α) (hl : l.Nodup) :
    (permutationWords l).card=l.length.factorial := by
  rw [permutationWords,List.toFinset_card_of_nodup (List.nodup_permutations l hl),
    List.length_permutations]

lemma markedEnd_take_succ {α : Type*} (N : α → Prop) (l : List α) (i : ℕ)
    (hi : i < l.length) : MarkedEnd N (l.take (i+1)) ↔ N l[i] := by
  rw [List.take_succ_eq_append_getElem hi]
  simp only [MarkedEnd,List.getLast?_concat,Option.some.injEq]
  constructor
  · rintro ⟨a,he,ha⟩
    exact he.symm ▸ ha
  · intro h
    exact ⟨l[i],rfl,h⟩

lemma markedEnd_take_pos {α : Type*} {N : α → Prop} {l : List α} {k : ℕ}
    (h : MarkedEnd N (l.take k)) : 0 < k := by
  by_contra hn
  have hk : k=0 := by omega
  rw [hk,List.take_zero] at h
  exact markedEnd_not_nil h rfl

lemma markedEnd_take_iff {α : Type*} (N : α → Prop) (l : List α) (k : ℕ)
    (hk : k ≤ l.length) :
    MarkedEnd N (l.take k) ↔ ∃ h : 0<k, N (l[k-1]'(by omega)) := by
  constructor
  · intro h
    have hp := markedEnd_take_pos h
    refine ⟨hp,?_⟩
    have hh := (markedEnd_take_succ N l (k-1) (by omega)).mp
      (show MarkedEnd N (l.take ((k-1)+1)) from by simpa only [Nat.sub_add_cancel hp] using h)
    exact hh
  · rintro ⟨hp,h⟩
    have hh := (markedEnd_take_succ N l (k-1) (by omega)).mpr h
    simpa only [Nat.sub_add_cancel hp] using hh

lemma marked_prefix_card {α : Type*} [DecidableEq α] (N : α → Prop)
    (l : List α) (hl : l.Nodup) :
    (Finset.filter (fun k => MarkedEnd N (l.take k)) (Finset.range (l.length+1))).card =
      (l.toFinset.filter N).card := by
  classical
  let F := Finset.filter (fun k => MarkedEnd N (l.take k)) (Finset.range (l.length+1))
  have hk : ∀ k ∈ F, k ≤ l.length := by
    intro k hk
    exact Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hk).1)
  have hp : ∀ k ∈ F, 0 < k := fun k hk => markedEnd_take_pos (Finset.mem_filter.mp hk).2
  let f : (k : ℕ) → k ∈ F → α := fun k h => l[k-1]'(by have := hk k h; have := hp k h; omega)
  apply Finset.card_bij f
  · intro k h
    refine Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (List.getElem_mem _),?_⟩
    exact ((markedEnd_take_iff N l k (hk k h)).mp (Finset.mem_filter.mp h).2).2
  · intro k h j hj he
    have hh : k-1=j-1 := hl.getElem_inj_iff.mp he
    have := hp k h
    have := hp j hj
    omega
  · intro a ha
    obtain ⟨haL,haN⟩ := Finset.mem_filter.mp ha
    obtain ⟨i,hi,hia⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp haL)
    have hm : MarkedEnd N (l.take (i+1)) := (markedEnd_take_succ N l i hi).mpr (hia.symm ▸ haN)
    have hF : i+1 ∈ F := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega),hm⟩
    refine ⟨i+1,hF,?_⟩
    simpa only [f,Nat.add_sub_cancel] using hia

lemma goodWordCuts_true_card {α : Type*} [DecidableEq α]
    (W : Finset (List α)) (m : ℕ) (N : α → Prop)
    (hlen : ∀ l ∈ W, l.length=m) (hnodup : ∀ l ∈ W, l.Nodup) :
    (goodWordCuts W m N (fun _ => True)).card =
      ∑ l ∈ W, (l.toFinset.filter N).card := by
  classical
  unfold goodWordCuts
  rw [Finset.card_filter,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro l hl
  simp only [and_true]
  rw [← Finset.card_filter,← hlen l hl,marked_prefix_card N l (hnodup l hl)]

lemma allowedWordCuts_card {α : Type*} [DecidableEq α]
    (W : Finset (List α)) (m : ℕ) (N : α → Prop) :
    (allowedWordCuts W m N).card = W.card+(goodWordCuts W m N (fun _ => True)).card := by
  classical
  let E := W.image (fun l => (l,0))
  have hdis : Disjoint E (goodWordCuts W m N (fun _ => True)) := by
    apply Finset.disjoint_left.mpr
    rintro p hp hgood
    obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hp
    simp only [goodWordCuts,Finset.mem_filter] at hgood
    have hm := hgood.2.1
    simp only [List.take_zero] at hm
    exact markedEnd_not_nil hm rfl
  have he : allowedWordCuts W m N = E ∪ goodWordCuts W m N (fun _ => True) := by
    ext p
    simp only [allowedWordCuts,goodWordCuts,Finset.mem_filter,Finset.mem_product,
      Finset.mem_range,Finset.mem_union,and_true]
    constructor
    · rintro ⟨⟨hl,hk⟩,he | hm⟩
      · exact Or.inl (Finset.mem_image.mpr ⟨p.1,hl,Prod.ext rfl he.symm⟩)
      · exact Or.inr ⟨⟨hl,hk⟩,hm⟩
    · rintro (hp | hp)
      · obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hp
        exact ⟨⟨hl,by omega⟩,Or.inl rfl⟩
      · exact ⟨hp.1,Or.inr hp.2⟩
  rw [he,Finset.card_union_of_disjoint hdis]
  congr 1
  exact Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)

end Erdos548

/- Full permutation words, grouped by their first letter. -/
namespace Erdos548
attribute [local instance] Classical.propDecidable

/-- The first letter is a distinguished root, and a marked cut is taken in
the remaining word. The family is allowed to depend on that root. -/
def FullWordQualifies {α : Type*} [DecidableEq α]
    (N : α → α → Prop) (A : α → Finset α → Prop) (l : List α) (k : ℕ) : Prop :=
  ∃ b q, l=b::q ∧ MarkedEnd (N b) (q.take k) ∧ A b (q.take k).toFinset

lemma fullWordQualifies_cons {α : Type*} [DecidableEq α]
    (N : α → α → Prop) (A : α → Finset α → Prop) (b : α) (q : List α) (k : ℕ) :
    FullWordQualifies N A (b::q) k ↔
      MarkedEnd (N b) (q.take k) ∧ A b (q.take k).toFinset := by
  constructor
  · rintro ⟨b',q',he,hm,hA⟩
    obtain ⟨rfl,rfl⟩ := List.cons.inj he
    exact ⟨hm,hA⟩
  · rintro ⟨hm,hA⟩
    exact ⟨b,q,rfl,hm,hA⟩

noncomputable def fullGoodWordCuts {α : Type*} [DecidableEq α]
    (l₀ : List α) (N : α → α → Prop) (A : α → Finset α → Prop) : Finset (List α × ℕ) :=
  (permutationWords l₀ ×ˢ Finset.range l₀.length).filter
    (fun p => FullWordQualifies N A p.1 p.2)

noncomputable def fullWordCount {α : Type*} [DecidableEq α]
    (l₀ : List α) (N : α → α → Prop) (A : α → Finset α → Prop) : ℕ :=
  (fullGoodWordCuts l₀ N A).card

lemma mem_fullGoodWordCuts {α : Type*} [DecidableEq α]
    (l₀ : List α) (N : α → α → Prop) (A : α → Finset α → Prop) (l : List α) (k : ℕ) :
    (l,k) ∈ fullGoodWordCuts l₀ N A ↔ l.Perm l₀ ∧ k<l₀.length ∧ FullWordQualifies N A l k := by
  simp only [fullGoodWordCuts,Finset.mem_filter,Finset.mem_product,mem_permutationWords,
    Finset.mem_range,and_assoc]

lemma fullWordCount_eq_sum {α : Type*} [DecidableEq α]
    (l₀ : List α) (N : α → α → Prop) (A : α → Finset α → Prop) :
    fullWordCount l₀ N A = ∑ b ∈ l₀.toFinset,
      (goodWordCuts (permutationWords (l₀.erase b)) (l₀.length-1) (N b) (A b)).card := by
  classical
  let F := fun b => goodWordCuts (permutationWords (l₀.erase b)) (l₀.length-1) (N b) (A b)
  let E := fun b => (F b).image (fun p => (b::p.1,p.2))
  have he : fullGoodWordCuts l₀ N A = l₀.toFinset.biUnion E := by
    ext p
    rcases p with ⟨l,k⟩
    rw [mem_fullGoodWordCuts,Finset.mem_biUnion]
    constructor
    · rintro ⟨hl,hk,b,q,rfl,hm,hA⟩
      obtain ⟨hb,hq⟩ := List.cons_perm_iff_perm_erase.mp hl
      refine ⟨b,List.mem_toFinset.mpr hb,Finset.mem_image.mpr ⟨(q,k),?_,rfl⟩⟩
      have hn : 0 < l₀.length := by have := List.length_pos_of_mem hb; omega
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨(mem_permutationWords _ _).mpr hq,Finset.mem_range.mpr (by omega)⟩,hm,hA⟩
    · rintro ⟨b,hb,hp⟩
      obtain ⟨⟨q,j⟩,hq,heq⟩ := Finset.mem_image.mp hp
      have hword : b::q=l := congrArg Prod.fst heq
      have hj : j=k := congrArg Prod.snd heq
      subst l
      subst j
      obtain ⟨hbase,hm,hA⟩ := Finset.mem_filter.mp hq
      obtain ⟨hq,hk⟩ := Finset.mem_product.mp hbase
      have hbL := List.mem_toFinset.mp hb
      have hn := List.length_pos_of_mem hbL
      refine ⟨List.cons_perm_iff_perm_erase.mpr ⟨hbL,(mem_permutationWords _ _).mp hq⟩,
        by have := Finset.mem_range.mp hk; omega,b,q,rfl,hm,hA⟩
  have hd : (l₀.toFinset : Set α).PairwiseDisjoint E := by
    intro b hb c hc hbc
    apply Finset.disjoint_left.mpr
    rintro p hp hq
    obtain ⟨⟨q,k⟩,_,he₁⟩ := Finset.mem_image.mp hp
    obtain ⟨⟨r,j⟩,_,he₂⟩ := Finset.mem_image.mp hq
    have hword := congrArg Prod.fst (he₁.trans he₂.symm)
    exact hbc (List.cons.inj hword).1
  unfold fullWordCount
  rw [he,Finset.card_biUnion hd]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.card_image_of_injective
  rintro ⟨q,k⟩ ⟨r,j⟩ h
  have hq := (List.cons.inj (congrArg Prod.fst h)).2
  have hk : k=j := congrArg Prod.snd h
  exact Prod.ext hq hk

/-- Sum of the numbers of outer words: exactly one full word for every
choice of its head and its outer permutation. -/
lemma sum_outer_words_card {α : Type*} [DecidableEq α] (l₀ : List α) (hl : l₀.Nodup)
    (hne : l₀ ≠ []) :
    (∑ b ∈ l₀.toFinset, (permutationWords (l₀.erase b)).card) = (permutationWords l₀).card := by
  classical
  have hn : 0 < l₀.length := List.length_pos_iff.mpr hne
  have he : ∀ b ∈ l₀.toFinset,
      (permutationWords (l₀.erase b)).card=(l₀.length-1).factorial := by
    intro b hb
    rw [permutationWords_card _ (hl.erase b),List.length_erase_of_mem (List.mem_toFinset.mp hb)]
  rw [Finset.sum_congr rfl he]
  simp only [Finset.sum_const,nsmul_eq_mul,List.toFinset_card_of_nodup hl,permutationWords_card l₀ hl]
  simpa only [Nat.sub_add_cancel hn] using (Nat.factorial_succ (l₀.length-1)).symm

/-- Root-dependent gluing, summed over ALL full permutation words. -/
lemma full_word_gluing_count {α : Type*} [DecidableEq α]
    (l₀ : List α) (hl : l₀.Nodup) (hne : l₀ ≠ [])
    (N : α → α → Prop) (A B C : α → Finset α → Prop)
    (hCA : ∀ b X, C b X → A b X)
    (hglue : ∀ b R X, Disjoint R X → A b R → B b X → C b (R ∪ X)) :
    fullWordCount l₀ N A + fullWordCount l₀ N B ≤
      fullWordCount l₀ N (fun _ _ => True) + (permutationWords l₀).card + fullWordCount l₀ N C := by
  classical
  have hh : ∀ b ∈ l₀.toFinset,
      (goodWordCuts (permutationWords (l₀.erase b)) (l₀.length-1) (N b) (A b)).card +
        (goodWordCuts (permutationWords (l₀.erase b)) (l₀.length-1) (N b) (B b)).card ≤
      (goodWordCuts (permutationWords (l₀.erase b)) (l₀.length-1) (N b) (fun _ => True)).card +
        (permutationWords (l₀.erase b)).card +
        (goodWordCuts (permutationWords (l₀.erase b)) (l₀.length-1) (N b) (C b)).card := by
    intro b hb
    have he := marked_word_gluing_count (permutationWords (l₀.erase b)) (l₀.length-1) (N b)
      (A b) (B b) (C b)
      (fun q hq => ((mem_permutationWords _ _).mp hq).length_eq.trans
        (List.length_erase_of_mem (List.mem_toFinset.mp hb)))
      (fun q hq => ((mem_permutationWords _ _).mp hq).nodup_iff.mpr (hl.erase b))
      (fun q hq q' hp => (mem_permutationWords _ _).mpr
        (hp.trans ((mem_permutationWords _ _).mp hq))) (hCA b) (hglue b)
    rw [allowedWordCuts_card] at he
    omega
  have hs := Finset.sum_le_sum hh
  simp only [Finset.sum_add_distrib] at hs
  rw [sum_outer_words_card l₀ hl hne] at hs
  simpa only [fullWordCount_eq_sum] using hs

end Erdos548

/- An involution on permutation words: reverse the initial block through a
cut and also reverse the remaining block. -/
namespace Erdos548

def reverseWordAt {α : Type*} (l : List α) (c : ℕ) : List α :=
  (l.take c).reverse ++ (l.drop c).reverse

lemma reverseWordAt_perm {α : Type*} (l : List α) (c : ℕ) : (reverseWordAt l c).Perm l := by
  have h := (List.reverse_perm (l.take c)).append (List.reverse_perm (l.drop c))
  simpa only [reverseWordAt,List.take_append_drop] using h

lemma reverseWordAt_involutive {α : Type*} (l : List α) (c : ℕ) :
    reverseWordAt (reverseWordAt l c) c=l := by
  by_cases hc : c ≤ l.length
  · have hrlen : (l.take c).reverse.length=c := by simp only [List.length_reverse,List.length_take]; omega
    have ht : (reverseWordAt l c).take c=(l.take c).reverse := by
      simpa only [reverseWordAt,hrlen] using
        (List.take_left (l₁:=(l.take c).reverse) (l₂:=(l.drop c).reverse))
    have hd : (reverseWordAt l c).drop c=(l.drop c).reverse := by
      simpa only [reverseWordAt,hrlen] using
        (List.drop_left (l₁:=(l.take c).reverse) (l₂:=(l.drop c).reverse))
    rw [reverseWordAt,ht,hd,List.reverse_reverse,List.reverse_reverse,List.take_append_drop]
  · have hlc : l.length ≤ c := by omega
    have he : reverseWordAt l c=l.reverse := by
      simp [reverseWordAt,List.take_of_length_le hlc,List.drop_eq_nil_of_le hlc]
    have hrc : l.reverse.length ≤ c := by simpa using hlc
    rw [he]
    simp [reverseWordAt,List.take_of_length_le hrc,List.drop_eq_nil_of_le hrc]

def reverseCutPair {α : Type*} (p : List α × ℕ) : List α × ℕ :=
  (reverseWordAt p.1 (p.2+1),p.2)

lemma reverseCutPair_involutive {α : Type*} : Function.Involutive (@reverseCutPair α) := by
  rintro ⟨l,k⟩
  exact Prod.ext (reverseWordAt_involutive l (k+1)) rfl

lemma reverseCutPair_injective {α : Type*} : Function.Injective (@reverseCutPair α) :=
  reverseCutPair_involutive.injective

lemma reverseWordAt_decomposition {α : Type*} (b w : α) (p q : List α) :
    reverseWordAt (b::(p++w::q)) (p.length+2) = w::(p.reverse++b::q.reverse) := by
  have he : b::(p++w::q) = (b::(p++[w]))++q := by simp only [List.cons_append,List.append_assoc,List.nil_append]
  have hlen : (b::(p++[w])).length=p.length+2 := by simp
  rw [he,← hlen,reverseWordAt,List.take_left,List.drop_left]
  simp only [List.reverse_cons,List.reverse_append,List.cons_append,
    List.nil_append,List.append_assoc,List.reverse_nil]

/-- A first-state loss of at most one per full word, followed by the cut
reversal involution. This is purely finite counting. -/
lemma full_word_transfer_count {α : Type*} [DecidableEq α]
    (l₀ : List α) (N N' : α → α → Prop) (A B : α → Finset α → Prop)
    (hstep : ∀ l, l.Perm l₀ → ∀ k, k<l₀.length → FullWordQualifies N A l k →
      ∀ j, j<k → FullWordQualifies N A l j →
        FullWordQualifies N' B (reverseWordAt l (k+1)) k) :
    fullWordCount l₀ N A ≤ fullWordCount l₀ N' B + (permutationWords l₀).card := by
  classical
  let D := fullGoodWordCuts l₀ N A
  let M := D.filter (fun p => ∃ j, j<p.2 ∧ FullWordQualifies N A p.1 j)
  have hMD : M ⊆ D := Finset.filter_subset _ _
  have hfirst : (D \ M).card ≤ (permutationWords l₀).card := by
    apply Finset.card_le_card_of_injOn Prod.fst
    · intro p hp
      have hpD := (Finset.mem_sdiff.mp hp).1
      exact (mem_permutationWords _ _).mpr ((mem_fullGoodWordCuts l₀ N A p.1 p.2).mp hpD).1
    · intro p hp q hq he
      have hpD := (mem_fullGoodWordCuts l₀ N A p.1 p.2).mp (Finset.mem_sdiff.mp hp).1
      have hqD := (mem_fullGoodWordCuts l₀ N A q.1 q.2).mp (Finset.mem_sdiff.mp hq).1
      apply Prod.ext he
      by_contra hn
      rcases lt_or_gt_of_ne hn with h | h
      · apply (Finset.mem_sdiff.mp hq).2
        exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hq).1,
          p.2,h,he ▸ hpD.2.2⟩
      · apply (Finset.mem_sdiff.mp hp).2
        exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hp).1,
          q.2,h,he.symm ▸ hqD.2.2⟩
  have hmove : M.card ≤ (fullGoodWordCuts l₀ N' B).card := by
    apply Finset.card_le_card_of_injOn reverseCutPair
    · rintro ⟨l,k⟩ hp
      obtain ⟨hpD,j,hjk,hj⟩ := Finset.mem_filter.mp hp
      obtain ⟨hl,hk,hs⟩ := (mem_fullGoodWordCuts l₀ N A l k).mp hpD
      exact (mem_fullGoodWordCuts l₀ N' B _ _).mpr
        ⟨(reverseWordAt_perm l (k+1)).trans hl,hk,hstep l hl k hk hs j hjk hj⟩
    · exact fun _ _ _ _ h => reverseCutPair_injective h
  have he := Finset.card_sdiff_add_card_eq_card hMD
  change D.card ≤ (fullGoodWordCuts l₀ N' B).card + (permutationWords l₀).card
  omega

end Erdos548

namespace Erdos548

/-- Attach a set of new leaves to a fixed vertex. -/
def attachLeaves {V : Type*} (S : SimpleGraph V) (r : V) (s : ℕ) :
    SimpleGraph (V ⊕ Fin s) where
  Adj
    | .inl a, .inl b => S.Adj a b
    | .inl a, .inr _ => a = r
    | .inr _, .inl b => b = r
    | .inr _, .inr _ => False
  symm := by rintro (a | a) (b | b) h <;> first | exact h.symm | exact h
  loopless := by constructor; rintro (a | a) <;> simp

end Erdos548

namespace Erdos548

lemma attach_single_leaf_copy {U V : Type*} (S : SimpleGraph U) (G : SimpleGraph V)
    (r : U) (f : S.Copy G) (w : V) (hw : G.Adj (f r) w) (hfree : w ∉ Set.range f) :
    ∃ F : (attachLeaves S r 1).Copy G,
      (∀ x, F (Sum.inl x) = f x) ∧ F (Sum.inr 0) = w := by
  classical
  let F : U ⊕ Fin 1 → V := Sum.elim f (fun _ => w)
  have hadj : ∀ x y, (attachLeaves S r 1).Adj x y → G.Adj (F x) (F y) := by
    rintro (x | x) (y | y) h
    · exact f.toHom.map_adj h
    · have he : x = r := h
      subst x
      exact hw
    · have he : y = r := h
      subst y
      exact hw.symm
    · exact h.elim
  have hinj : Function.Injective F := by
    rintro (x | x) (y | y) h
    · exact congrArg Sum.inl (f.injective h)
    · exact (hfree ⟨x,h⟩).elim
    · exact (hfree ⟨y,h.symm⟩).elim
    · exact congrArg Sum.inr (Subsingleton.elim _ _)
  exact ⟨⟨⟨F,fun {x y} h => hadj x y h⟩,hinj⟩,fun _ => rfl,rfl⟩


end Erdos548

/- Rooted graph copies in permutation-word prefixes, and a verified leaf-root
extension by an involution on the full words. -/
open SimpleGraph
namespace Erdos548

/-- A rooted copy supported on the root image and the displayed outer set. -/
def RootedWordFamily {U V : Type*} [DecidableEq V]
    (S : SimpleGraph U) (r : U) (G : SimpleGraph V) (b : V) (X : Finset V) : Prop :=
  ∃ f : S.Copy G, f r=b ∧ ∀ x, f x ∈ insert b X

noncomputable def rootedWordCount {U V : Type*} [DecidableEq V]
    (S : SimpleGraph U) (r : U) (G : SimpleGraph V) (l₀ : List V) : ℕ :=
  fullWordCount l₀ G.Adj (RootedWordFamily S r G)

lemma rootedWordFamily_mono {U V : Type*} [DecidableEq V]
    (S : SimpleGraph U) (r : U) (G : SimpleGraph V) (b : V) {X Y : Finset V}
    (hXY : X ⊆ Y) : RootedWordFamily S r G b X → RootedWordFamily S r G b Y := by
  rintro ⟨f,hfr,hspan⟩
  exact ⟨f,hfr,fun x => (Finset.insert_subset_insert _ hXY) (hspan x)⟩

lemma rooted_word_leaf_move_step {U V : Type*} [DecidableEq V]
    (S : SimpleGraph U) (r : U) (G : SimpleGraph V) (l : List V) (hl : l.Nodup)
    (k : ℕ) (hk : k<l.length)
    (hs : FullWordQualifies G.Adj (RootedWordFamily S r G) l k)
    (j : ℕ) (hjk : j<k)
    (hj : FullWordQualifies G.Adj (RootedWordFamily S r G) l j) :
    FullWordQualifies G.Adj (RootedWordFamily (attachLeaves S r 1) (Sum.inr 0) G)
      (reverseWordAt l (k+1)) k := by
  classical
  obtain ⟨b,q,rfl,hm,_⟩ := hs
  have hkq : k ≤ q.length := by simpa only [List.length_cons,Nat.lt_add_one_iff] using hk
  have hj' := (fullWordQualifies_cons G.Adj (RootedWordFamily S r G) b q j).mp hj
  obtain ⟨f,hfr,hspan⟩ := hj'.2
  obtain ⟨w,hw,hbw⟩ := hm
  obtain ⟨p,hp⟩ := List.getLast?_eq_some_iff.mp hw
  let z := q.drop k
  have hq : q=p++w::z := by
    have he := List.take_append_drop k q
    rw [hp] at he
    simpa only [List.append_assoc,List.singleton_append] using he.symm
  have hpk : p.length+1=k := by
    have he := congrArg List.length hp
    simp only [List.length_take,List.length_append,List.length_singleton] at he
    omega
  have hjp : j ≤ p.length := by omega
  have htakej : q.take j=p.take j := by
    rw [hq,List.take_append_of_le_length hjp]
  have hnq : q.Nodup := (List.nodup_cons.mp hl).2
  have hnd : (p++w::z).Nodup := hq ▸ hnq
  have hwP : w ∉ p := by
    intro hh
    exact (List.disjoint_left.mp hnd.disjoint) hh List.mem_cons_self
  have hfree : w ∉ Set.range f := by
    rintro ⟨x,hx⟩
    have hh := hspan x
    rw [hx] at hh
    rcases Finset.mem_insert.mp hh with he | he
    · exact hbw.ne he.symm
    · rw [htakej] at he
      exact hwP (List.mem_of_mem_take (List.mem_toFinset.mp he))
  obtain ⟨F,hF,hFw⟩ := attach_single_leaf_copy S G r f w (by rw [hfr]; exact hbw) hfree
  have hrev : reverseWordAt (b::q) (k+1)=w::(p.reverse++b::z.reverse) := by
    rw [hq,← hpk]
    simpa only [Nat.add_assoc] using reverseWordAt_decomposition b w p z
  have hnewtake : (p.reverse++b::z.reverse).take k=p.reverse++[b] := by
    have he : p.reverse++b::z.reverse=(p.reverse++[b])++z.reverse := by
      simp only [List.append_assoc,List.singleton_append]
    have hlen : (p.reverse++[b]).length=k := by
      simp only [List.length_append,List.length_reverse,List.length_singleton]
      exact hpk
    rw [he,← hlen,List.take_left]
  rw [hrev]
  apply (fullWordQualifies_cons G.Adj _ _ _ _).mpr
  constructor
  · rw [hnewtake]
    exact ⟨b,List.getLast?_concat,hbw.symm⟩
  · refine ⟨F,hFw,?_⟩
    rintro (x | x)
    · rw [hF x,hnewtake]
      apply Finset.mem_insert_of_mem
      have hh := hspan x
      rcases Finset.mem_insert.mp hh with hx | hx
      · rw [hx]
        exact List.mem_toFinset.mpr (List.mem_append_right _ (List.mem_singleton_self _))
      · rw [htakej] at hx
        apply List.mem_toFinset.mpr
        apply List.mem_append_left
        exact List.mem_reverse.mpr (List.mem_of_mem_take (List.mem_toFinset.mp hx))
    · have hx : x=0 := Subsingleton.elim _ _
      subst x
      rw [hFw]
      exact Finset.mem_insert_self _ _

lemma rooted_word_leaf_move_count {U V : Type*} [DecidableEq V]
    (S : SimpleGraph U) (r : U) (G : SimpleGraph V) (l₀ : List V) (hl : l₀.Nodup) :
    rootedWordCount S r G l₀ ≤
      rootedWordCount (attachLeaves S r 1) (Sum.inr 0) G l₀ + (permutationWords l₀).card := by
  apply full_word_transfer_count
  intro l hlp k hk hs j hjk hj
  exact rooted_word_leaf_move_step S r G l (hlp.nodup_iff.mpr hl) k
    (by rwa [hlp.length_eq]) hs j hjk hj

end Erdos548

/- Rooted copies on two branches meeting at one root, and the corresponding
exact permutation-word counting inequality. -/
open SimpleGraph
namespace Erdos548

lemma rootedWordFamily_iso_iff {U W V : Type*} [DecidableEq V]
    {S : SimpleGraph U} {T : SimpleGraph W} (e : S ≃g T) (r : U)
    (G : SimpleGraph V) (b : V) (X : Finset V) :
    RootedWordFamily T (e r) G b X ↔ RootedWordFamily S r G b X := by
  constructor
  · rintro ⟨f,hfr,hspan⟩
    exact ⟨f.comp e.toCopy,hfr,fun x => hspan (e x)⟩
  · rintro ⟨f,hfr,hspan⟩
    refine ⟨f.comp e.symm.toCopy,?_,fun x => hspan (e.symm x)⟩
    simpa using hfr

lemma rootedWordCount_iso {U W V : Type*} [DecidableEq V]
    {S : SimpleGraph U} {T : SimpleGraph W} (e : S ≃g T) (r : U)
    (G : SimpleGraph V) (l₀ : List V) :
    rootedWordCount T (e r) G l₀=rootedWordCount S r G l₀ := by
  have he : RootedWordFamily T (e r) G=RootedWordFamily S r G := by
    funext b X
    exact propext (rootedWordFamily_iso_iff e r G b X)
  unfold rootedWordCount
  rw [he]

lemma rootedWordFamily_restrict {U V : Type*} [DecidableEq V]
    (T : SimpleGraph U) (G : SimpleGraph V) (A : Set U) (r : U) (hr : r ∈ A)
    (b : V) (X : Finset V) : RootedWordFamily T r G b X →
      RootedWordFamily (T.induce A) ⟨r,hr⟩ G b X := by
  rintro ⟨f,hfr,hspan⟩
  exact ⟨f.comp (Copy.induce T A),hfr,fun x => hspan x.val⟩

/-- Two copies agree at the root. Disjoint outer supporting sets ensure that
no other images collide. -/
lemma rootedWordFamily_glue {U V : Type*} [DecidableEq V]
    (T : SimpleGraph U) (G : SimpleGraph V) (A : Set U) (r : U) (hr : r ∈ A)
    (hsep : ∀ x ∈ A, ∀ y ∉ A, T.Adj x y → x=r)
    (b : V) (R X : Finset V) (hd : Disjoint R X)
    (hf : RootedWordFamily (T.induce A) ⟨r,hr⟩ G b R)
    (hg : RootedWordFamily (T.induce (Aᶜ ∪ {r})) ⟨r,Or.inr rfl⟩ G b X) :
    RootedWordFamily T r G b (R ∪ X) := by
  classical
  obtain ⟨f,hfr,hfspan⟩ := hf
  obtain ⟨g,hgr,hgspan⟩ := hg
  let F : U → V := fun x => if hx : x ∈ A then f ⟨x,hx⟩ else g ⟨x,Or.inl hx⟩
  have hcross : ∀ x : A, ∀ y : (Aᶜ ∪ {r} : Set U), y.val ∉ A → f x ≠ g y := by
    intro x y hy he
    have hgneq : g y ≠ b := by
      intro hb
      have hy' : y=⟨r,Or.inr rfl⟩ := g.injective (hb.trans hgr.symm)
      exact hy (by simpa only [hy'] using hr)
    have hfR : f x ∈ R := (Finset.mem_insert.mp (hfspan x)).resolve_left (fun hh => hgneq (he.symm.trans hh))
    have hgX : g y ∈ X := (Finset.mem_insert.mp (hgspan y)).resolve_left hgneq
    exact Finset.disjoint_left.mp hd hfR (he.symm ▸ hgX)
  have hmap : ∀ {x y}, T.Adj x y → G.Adj (F x) (F y) := by
    intro x y hxy
    by_cases hx : x ∈ A <;> by_cases hy : y ∈ A
    · simpa only [F,dif_pos hx,dif_pos hy] using
        (show G.Adj (f ⟨x,hx⟩) (f ⟨y,hy⟩) from f.toHom.map_adj hxy)
    · have hxr := hsep x hx y hy hxy
      subst x
      have he := g.toHom.map_adj (show (T.induce (Aᶜ ∪ {r})).Adj
        ⟨r,Or.inr rfl⟩ ⟨y,Or.inl hy⟩ from hxy)
      change G.Adj (g ⟨r,Or.inr rfl⟩) (g ⟨y,Or.inl hy⟩) at he
      simpa only [F,dif_pos hr,dif_neg hy,hfr,hgr] using he
    · have hyr := hsep y hy x hx hxy.symm
      subst y
      have he := g.toHom.map_adj (show (T.induce (Aᶜ ∪ {r})).Adj
        ⟨x,Or.inl hx⟩ ⟨r,Or.inr rfl⟩ from hxy)
      change G.Adj (g ⟨x,Or.inl hx⟩) (g ⟨r,Or.inr rfl⟩) at he
      simpa only [F,dif_neg hx,dif_pos hr,hfr,hgr] using he
    · simpa only [F,dif_neg hx,dif_neg hy] using
        (show G.Adj (g ⟨x,Or.inl hx⟩) (g ⟨y,Or.inl hy⟩) from g.toHom.map_adj hxy)
  have hinj : Function.Injective F := by
    intro x y he
    by_cases hx : x ∈ A <;> by_cases hy : y ∈ A
    · have he' : f ⟨x,hx⟩=f ⟨y,hy⟩ := by simpa only [F,dif_pos hx,dif_pos hy] using he
      exact congrArg Subtype.val (f.injective he')
    · exact (hcross ⟨x,hx⟩ ⟨y,Or.inl hy⟩ hy (by simpa only [F,dif_pos hx,dif_neg hy] using he)).elim
    · exact (hcross ⟨y,hy⟩ ⟨x,Or.inl hx⟩ hx (by simpa only [F,dif_neg hx,dif_pos hy] using he.symm)).elim
    · have he' : g ⟨x,Or.inl hx⟩=g ⟨y,Or.inl hy⟩ := by simpa only [F,dif_neg hx,dif_neg hy] using he
      exact congrArg Subtype.val (g.injective he')
  refine ⟨⟨⟨F,hmap⟩,hinj⟩,?_,?_⟩
  · change F r = b
    simpa only [F,dif_pos hr] using hfr
  · intro x
    by_cases hx : x ∈ A
    · change F x ∈ _
      rw [show F x=f ⟨x,hx⟩ by simp only [F,dif_pos hx]]
      exact Finset.insert_subset_insert b Finset.subset_union_left (hfspan ⟨x,hx⟩)
    · change F x ∈ _
      rw [show F x=g ⟨x,Or.inl hx⟩ by simp only [F,dif_neg hx]]
      exact Finset.insert_subset_insert b Finset.subset_union_right (hgspan ⟨x,Or.inl hx⟩)

lemma rooted_word_branch_gluing_count {U V : Type*} [DecidableEq V]
    (T : SimpleGraph U) (G : SimpleGraph V) (A : Set U) (r : U) (hr : r ∈ A)
    (hsep : ∀ x ∈ A, ∀ y ∉ A, T.Adj x y → x=r)
    (l₀ : List V) (hl : l₀.Nodup) (hne : l₀ ≠ []) :
    rootedWordCount (T.induce A) ⟨r,hr⟩ G l₀ +
      rootedWordCount (T.induce (Aᶜ ∪ {r})) ⟨r,Or.inr rfl⟩ G l₀ ≤
      fullWordCount l₀ G.Adj (fun _ _ => True)+(permutationWords l₀).card+rootedWordCount T r G l₀ := by
  apply full_word_gluing_count l₀ hl hne
  · exact rootedWordFamily_restrict T G A r hr
  · exact rootedWordFamily_glue T G A r hr hsep

end Erdos548

namespace Erdos548

lemma tree_edge_partition {U : Type} (T : SimpleGraph U) (hT : T.IsTree)
    (r s : U) (hrs : T.Adj r s) :
    ∃ A : Set U, r ∈ A ∧ s ∉ A ∧ (T.induce A).IsTree ∧ (T.induce Aᶜ).IsTree ∧
      ∀ x ∈ A, ∀ y ∉ A, T.Adj x y → x=r ∧ y=s := by
  classical
  let D := T \ fromEdgeSet {s(r,s)}
  have hno : ¬D.Reachable r s :=
    (isBridge_iff.mp ((isAcyclic_iff_forall_adj_isBridge.mp hT.IsAcyclic) hrs)).2
  have hdeleted : ∀ {x y}, T.Adj x y → ¬D.Adj x y →
      (x=r ∧ y=s) ∨ (x=s ∧ y=r) := by
    intro x y hxy hn
    have he : s(x,y)=s(r,s) := by
      by_contra he
      apply hn
      exact ⟨hxy,by simp [fromEdgeSet_adj,he]⟩
    exact Sym2.eq_iff.mp he
  have hwalk : ∀ {x y} (p : T.Walk x y),
      (D.Reachable r y ∨ D.Reachable s y) → (D.Reachable r x ∨ D.Reachable s x) := by
    intro x y p
    induction p with
    | nil => exact fun h => h
    | @cons x y z hxy p ih =>
      intro h
      have hy := ih h
      by_cases he : D.Adj x y
      · exact hy.elim (fun h => Or.inl (h.trans he.symm.reachable))
          (fun h => Or.inr (h.trans he.symm.reachable))
      · rcases hdeleted hxy he with ⟨rfl,_⟩ | ⟨rfl,_⟩
        · exact Or.inl Reachable.rfl
        · exact Or.inr Reachable.rfl
  have hcover : ∀ x, D.Reachable r x ∨ D.Reachable s x := by
    intro x
    obtain ⟨p⟩ := hT.isConnected.preconnected x r
    exact hwalk p (Or.inl Reachable.rfl)
  let A := (D.connectedComponentMk r).supp
  have hmem : ∀ x, x ∈ A ↔ D.Reachable r x := by
    intro x
    simp only [A,ConnectedComponent.mem_supp_iff,ConnectedComponent.eq,D.reachable_comm]
  have hrA : r ∈ A := (hmem r).mpr Reachable.rfl
  have hsA : s ∉ A := fun h => hno ((hmem s).mp h)
  have hAc : Aᶜ=(D.connectedComponentMk s).supp := by
    ext x
    simp only [Set.mem_compl_iff,ConnectedComponent.mem_supp_iff,ConnectedComponent.eq]
    constructor
    · intro hx
      exact ((hcover x).resolve_left (fun h => hx ((hmem x).mpr h))).symm
    · intro hx hxa
      exact hno (((hmem x).mp hxa).trans hx)
  have hAconn : (T.induce A).Connected :=
    Connected.mono (show D.induce A ≤ T.induce A from fun _ _ h => h.1)
      (D.connectedComponentMk r).connected_toSimpleGraph
  have hAcconn : (T.induce Aᶜ).Connected := by
    rw [hAc]
    exact Connected.mono (show D.induce (D.connectedComponentMk s).supp ≤
      T.induce (D.connectedComponentMk s).supp from fun _ _ h => h.1)
      (D.connectedComponentMk s).connected_toSimpleGraph
  refine ⟨A,hrA,hsA,⟨hAconn,hT.IsAcyclic.induce A⟩,
    ⟨hAcconn,hT.IsAcyclic.induce Aᶜ⟩,?_⟩
  intro x hx y hy hxy
  have hn : ¬D.Adj x y := by
    intro h
    exact hy ((hmem y).mpr (((hmem x).mp hx).trans h.reachable))
  rcases hdeleted hxy hn with h | ⟨rfl,rfl⟩
  · exact h
  · exact (hsA hx).elim

end Erdos548

/- A nonleaf root splits a finite tree into two smaller rooted trees. -/
open SimpleGraph
namespace Erdos548

lemma tree_root_partition {U : Type} [Finite U] (T : SimpleGraph U) (hT : T.IsTree)
    (r s z : U) (hrs : T.Adj r s) (hrz : T.Adj r z) (hsz : s ≠ z) :
    ∃ A : Set U, ∃ _hr : r ∈ A,
      (T.induce A).IsTree ∧ (T.induce (Aᶜ ∪ {r})).IsTree ∧
      2 ≤ Nat.card A ∧ 2 ≤ Nat.card (Aᶜ ∪ {r} : Set U) ∧
      Nat.card A < Nat.card U ∧ Nat.card (Aᶜ ∪ {r} : Set U) < Nat.card U ∧
      Nat.card A + Nat.card (Aᶜ ∪ {r} : Set U) = Nat.card U + 1 ∧
      ∀ x ∈ A, ∀ y ∉ A, T.Adj x y → x=r := by
  classical
  obtain ⟨A,hr,hs,hA,hAc,hcut⟩ := tree_edge_partition T hT r s hrs
  have hz : z ∈ A := by
    by_contra hz
    exact hsz (hcut r hr z hz hrz).2.symm
  have hB : (T.induce (Aᶜ ∪ {r})).IsTree := by
    exact ⟨connected_induce_union hAc.isConnected.preconnected
      Preconnected.of_subsingleton hs (Set.mem_singleton r) hrs.symm,
      hT.IsAcyclic.induce _⟩
  have hA2 : 2 ≤ A.ncard := by
    have hh : ({r,z} : Set U) ⊆ A := by simpa only [Set.insert_subset_iff,Set.singleton_subset_iff] using And.intro hr hz
    simpa only [Set.ncard_pair hrz.ne] using Set.ncard_le_ncard hh
  have hB2 : 2 ≤ (Aᶜ ∪ {r}).ncard := by
    have hh : ({s,r} : Set U) ⊆ Aᶜ ∪ {r} := by
      simp only [Set.insert_subset_iff,Set.singleton_subset_iff,Set.mem_union,Set.mem_compl_iff,Set.mem_singleton_iff]
      exact ⟨Or.inl hs,Or.inr trivial⟩
    simpa only [Set.ncard_pair hrs.ne.symm] using Set.ncard_le_ncard hh
  have hAlt : A.ncard < Nat.card U := Set.ncard_lt_card (by
    intro he
    exact hs (he ▸ Set.mem_univ s))
  have hBlt : (Aᶜ ∪ {r}).ncard < Nat.card U := Set.ncard_lt_card (by
    intro he
    have hm : z ∈ Aᶜ ∪ {r} := he ▸ Set.mem_univ z
    exact hm.elim (fun hh => hh hz) hrz.ne.symm)
  have hcard : A.ncard + (Aᶜ ∪ {r}).ncard = Nat.card U+1 := by
    rw [Set.union_singleton,Set.ncard_insert_of_notMem (by simpa using hr)]
    rw [← Nat.add_assoc,Set.ncard_add_ncard_compl]
  exact ⟨A,hr,hA,hB,hA2,hB2,hAlt,hBlt,hcard,fun x hx y hy hxy => (hcut x hx y hy hxy).1⟩

end Erdos548

/- Every marked word cut supports any rooted graph of order two. -/
open SimpleGraph
namespace Erdos548

lemma rootedWordFamily_of_card_two {U V : Type*} [Fintype U] [DecidableEq V]
    (T : SimpleGraph U) (r : U) (ht : Fintype.card U = 2)
    (G : SimpleGraph V) (b w : V) (hbw : G.Adj b w) (X : Finset V) (hw : w ∈ X) :
    RootedWordFamily T r G b X := by
  classical
  have hc : Fintype.card ({r}ᶜ : Set U) ≤ 1 := by
    rw [Fintype.card_compl_set,ht]
    simp
  haveI : Subsingleton ({r}ᶜ : Set U) := Fintype.card_le_one_iff_subsingleton.mp hc
  have hnonroot : ∀ x y : U, x ≠ r → y ≠ r → x=y := by
    intro x y hx hy
    exact congrArg Subtype.val (Subsingleton.elim (⟨x,hx⟩ : ({r}ᶜ : Set U)) ⟨y,hy⟩)
  let F : U → V := fun x => if x=r then b else w
  have hinj : Function.Injective F := by
    intro x y he
    by_cases hx : x=r <;> by_cases hy : y=r
    · exact hx.trans hy.symm
    · exact (hbw.ne (by simpa only [F,if_pos hx,if_neg hy] using he)).elim
    · exact (hbw.ne.symm (by simpa only [F,if_neg hx,if_pos hy] using he)).elim
    · exact hnonroot x y hx hy
  have hadj : ∀ {x y}, T.Adj x y → G.Adj (F x) (F y) := by
    intro x y hxy
    by_cases hx : x=r <;> by_cases hy : y=r
    · exact (hxy.ne (hx.trans hy.symm)).elim
    · simpa only [F,if_pos hx,if_neg hy] using hbw
    · simpa only [F,if_neg hx,if_pos hy] using hbw.symm
    · exact (hxy.ne (hnonroot x y hx hy)).elim
  refine ⟨⟨⟨F,hadj⟩,hinj⟩,?_,?_⟩
  · change F r=b
    simp only [F,if_pos rfl]
  · intro x
    change F x ∈ _
    by_cases hx : x=r
    · simp only [F,if_pos hx,Finset.mem_insert_self]
    · simpa only [F,if_neg hx] using Finset.mem_insert_of_mem hw

lemma rooted_word_count_base {U V : Type*} [Fintype U] [DecidableEq V]
    (T : SimpleGraph U) (r : U) (ht : Fintype.card U = 2)
    (G : SimpleGraph V) (l₀ : List V) :
    fullWordCount l₀ G.Adj (fun _ _ => True) ≤ rootedWordCount T r G l₀ := by
  classical
  apply Finset.card_le_card
  intro p hp
  obtain ⟨hl,hk,b,q,he,hm,_⟩ := (mem_fullGoodWordCuts _ _ _ _ _).mp hp
  obtain ⟨w,hw,hbw⟩ := hm
  refine (mem_fullGoodWordCuts _ _ _ _ _).mpr ⟨hl,hk,b,q,he,⟨w,hw,hbw⟩,?_⟩
  apply rootedWordFamily_of_card_two T r ht G b w hbw
  exact List.mem_toFinset.mpr (List.mem_of_mem_getLast? (by simpa only [hw] using (show w ∈ some w from rfl)))

end Erdos548

namespace Erdos548

noncomputable def leafRestoreIso {U : Type} (T : SimpleGraph U) (l p : U)
    (hlp : T.Adj l p) (honly : ∀ x, T.Adj l x → x = p) :
    attachLeaves (T.induce {l}ᶜ) ⟨p,hlp.ne.symm⟩ 1 ≃g T := by
  classical
  let f : ({l}ᶜ : Set U) ⊕ Fin 1 → U := Sum.elim Subtype.val (fun _ => l)
  let g : U → ({l}ᶜ : Set U) ⊕ Fin 1 := fun x => if hx : x = l then Sum.inr 0 else Sum.inl ⟨x,hx⟩
  have hfg : Function.RightInverse g f := by
    intro x
    by_cases hx : x = l <;> simp [f,g,hx]
  have hgf : Function.LeftInverse g f := by
    rintro (x | x)
    · have hx : x.val ≠ l := x.property
      simp only [f,Sum.elim_inl,g,dif_neg hx,Subtype.coe_eta]
    · have hx : x = 0 := Subsingleton.elim _ _
      subst x
      simp only [f,Sum.elim_inr,g,dif_pos rfl]
  refine ⟨⟨f,g,hgf,hfg⟩,?_⟩
  rintro (x | x) (y | y)
  · rfl
  · change T.Adj x.val l ↔ x = ⟨p,hlp.ne.symm⟩
    constructor
    · exact fun h => Subtype.ext (honly x.val h.symm)
    · intro h
      rw [h]
      exact hlp.symm
  · change T.Adj l y.val ↔ y = ⟨p,hlp.ne.symm⟩
    constructor
    · exact fun h => Subtype.ext (honly y.val h)
    · intro h
      rw [h]
      exact hlp
  · change T.Adj l l ↔ False
    simp

@[simp] lemma leafRestoreIso_inl {U : Type} (T : SimpleGraph U) (l p : U)
    (hlp : T.Adj l p) (honly : ∀ x, T.Adj l x → x = p) (x : ({l}ᶜ : Set U)) :
    leafRestoreIso T l p hlp honly (Sum.inl x) = x.val := rfl

@[simp] lemma leafRestoreIso_inr {U : Type} (T : SimpleGraph U) (l p : U)
    (hlp : T.Adj l p) (honly : ∀ x, T.Adj l x → x = p) :
    leafRestoreIso T l p hlp honly (Sum.inr 0) = l := rfl

end Erdos548

/- The rooted word-count bound for every finite tree. -/
open SimpleGraph
namespace Erdos548
set_option maxHeartbeats 1000000

lemma rooted_word_tree_bound_aux (t : ℕ) :
    ∀ (U V : Type) [Fintype U] [DecidableEq V]
      (T : SimpleGraph U) (r : U) (_hT : T.IsTree) (_ht : Fintype.card U=t) (_ht2 : 2 ≤ t)
      (G : SimpleGraph V) (l₀ : List V) (_hl : l₀.Nodup) (_hne : l₀ ≠ []),
      fullWordCount l₀ G.Adj (fun _ _ => True) ≤
        rootedWordCount T r G l₀ + (t-2)*(permutationWords l₀).card := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro U V _ _ T r hT ht ht2 G l₀ hl hne
    classical
    by_cases htbase : t=2
    · have hcard2 : Fintype.card U=2 := ht.trans htbase
      simpa only [htbase,Nat.sub_self,Nat.zero_mul,Nat.add_zero] using rooted_word_count_base T r hcard2 G l₀
    have ht3 : 3 ≤ t := by omega
    haveI : Nontrivial U := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨s,hrs⟩ := hT.isConnected.preconnected.exists_adj_of_nontrivial r
    by_cases hleaf : ∀ z, T.Adj r z → z=s
    · have hdeg : T.degree r=1 := degree_eq_one_iff_existsUnique_adj.mpr ⟨s,hrs,hleaf⟩
      let A : Set U := {r}ᶜ
      let a : A := ⟨s,hrs.ne.symm⟩
      have hTA : (T.induce A).IsTree :=
        ⟨hT.isConnected.induce_compl_singleton_of_degree_eq_one hdeg,hT.IsAcyclic.induce A⟩
      have hcard : Fintype.card A=t-1 := by
        simp only [A,Fintype.card_compl_set,Fintype.card_unique,ht]
      have hsmall : Fintype.card A<t := by omega
      have htwo : 2 ≤ Fintype.card A := by omega
      have hbound := ih (Fintype.card A) hsmall A V (T.induce A) a hTA rfl htwo G l₀ hl hne
      have hmove := rooted_word_leaf_move_count (T.induce A) a G l₀ hl
      have hiso := rootedWordCount_iso (leafRestoreIso T r s hrs hleaf) (Sum.inr 0) G l₀
      rw [leafRestoreIso_inr] at hiso
      change rootedWordCount T r G l₀ = rootedWordCount (attachLeaves (T.induce A) a 1) (Sum.inr 0) G l₀ at hiso
      rw [← hiso] at hmove
      have hcoeff : Fintype.card A-2+1=t-2 := by omega
      have hcost := congrArg (fun j => j*(permutationWords l₀).card) hcoeff
      simp only [Nat.add_mul,Nat.one_mul] at hcost
      omega
    · push_neg at hleaf
      obtain ⟨z,hrz,hzs⟩ := hleaf
      obtain ⟨A,hr,hA,hB,hA2,hB2,hAlt,hBlt,hcard,hsep⟩ :=
        tree_root_partition T hT r s z hrs hrz hzs.symm
      simp only [Nat.card_eq_fintype_card,ht] at hAlt hBlt hcard
      simp only [Nat.card_eq_fintype_card] at hA2 hB2
      have hboundA := ih (Fintype.card A) hAlt A V (T.induce A) ⟨r,hr⟩ hA rfl hA2 G l₀ hl hne
      have hboundB := ih (Fintype.card (Aᶜ ∪ {r} : Set U)) hBlt (Aᶜ ∪ {r} : Set U) V
        (T.induce (Aᶜ ∪ {r})) ⟨r,Or.inr rfl⟩ hB rfl hB2 G l₀ hl hne
      have hglue := rooted_word_branch_gluing_count T G A r hr hsep l₀ hl hne
      have hcoeff : (Fintype.card A-2)+(Fintype.card (Aᶜ ∪ {r} : Set U)-2)+1=t-2 := by omega
      have hcost := congrArg (fun j => j*(permutationWords l₀).card) hcoeff
      simp only [Nat.add_mul,Nat.one_mul] at hcost
      omega

lemma rooted_word_tree_bound {U V : Type} [Fintype U] [DecidableEq V]
    (T : SimpleGraph U) (r : U) (hT : T.IsTree) (ht2 : 2 ≤ Fintype.card U)
    (G : SimpleGraph V) (l₀ : List V) (hl : l₀.Nodup) (hne : l₀ ≠ []) :
    fullWordCount l₀ G.Adj (fun _ _ => True) ≤
      rootedWordCount T r G l₀ + (Fintype.card U-2)*(permutationWords l₀).card :=
  rooted_word_tree_bound_aux (Fintype.card U) U V T r hT rfl ht2 G l₀ hl hne

end Erdos548

/- Exact host counts for a word containing every vertex once. -/
open SimpleGraph
namespace Erdos548

lemma full_word_base_count {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (l₀ : List V) (hl : l₀.Nodup) (hall : ∀ b, b ∈ l₀) :
    fullWordCount l₀ G.Adj (fun _ _ => True) =
      (l₀.length-1).factorial * (2*G.edgeSet.ncard) := by
  classical
  have hset : l₀.toFinset=Finset.univ := by
    ext b
    simp only [List.mem_toFinset,Finset.mem_univ,iff_true]
    exact hall b
  have hfiber : ∀ b ∈ l₀.toFinset,
      (goodWordCuts (permutationWords (l₀.erase b)) (l₀.length-1) (G.Adj b) (fun _ => True)).card =
        (l₀.length-1).factorial * G.degree b := by
    intro b hb
    have hlen : ∀ q ∈ permutationWords (l₀.erase b), q.length=l₀.length-1 := by
      intro q hq
      rw [((mem_permutationWords _ _).mp hq).length_eq,List.length_erase_of_mem (hall b)]
    have hnodup : ∀ q ∈ permutationWords (l₀.erase b), q.Nodup := by
      intro q hq
      exact ((mem_permutationWords _ _).mp hq).nodup_iff.mpr (hl.erase b)
    rw [goodWordCuts_true_card _ _ _ hlen hnodup]
    have hterm : ∀ q ∈ permutationWords (l₀.erase b), (q.toFinset.filter (G.Adj b)).card=G.degree b := by
      intro q hq
      have hp : (b::q).Perm l₀ := List.cons_perm_iff_perm_erase.mpr
        ⟨hall b,(mem_permutationWords _ _).mp hq⟩
      have he : q.toFinset.filter (G.Adj b)=G.neighborFinset b := by
        ext v
        simp only [Finset.mem_filter,List.mem_toFinset,G.mem_neighborFinset]
        constructor
        · exact And.right
        · intro hv
          constructor
          · have hm : v ∈ b::q := hp.mem_iff.mpr (hall v)
            exact (List.mem_cons.mp hm).resolve_left (fun hh => hv.ne hh.symm)
          · exact hv
      rw [he,G.card_neighborFinset_eq_degree]
    rw [Finset.sum_congr rfl hterm]
    simp only [Finset.sum_const,nsmul_eq_mul,permutationWords_card _ (hl.erase b),
      List.length_erase_of_mem (hall b),Nat.cast_id]
  rw [fullWordCount_eq_sum,Finset.sum_congr rfl hfiber,← Finset.mul_sum,hset,
    G.sum_degrees_eq_twice_card_edges]
  congr 2
  rw [edgeFinset_card,← Nat.card_eq_fintype_card]
  rfl

lemma rooted_word_count_zero_of_not_contained {U V : Type*} [DecidableEq V]
    (T : SimpleGraph U) (r : U) (G : SimpleGraph V) (h : ¬T.IsContained G) (l₀ : List V) :
    rootedWordCount T r G l₀=0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  rintro ⟨l,k⟩ hp
  obtain ⟨_,_,b,q,_,_,f,_,_⟩ := (mem_fullGoodWordCuts _ _ _ _ _).mp hp
  exact h ⟨f⟩

lemma tree_free_edge_bound {U V : Type} [Fintype U] [Fintype V]
    (T : SimpleGraph U) (hT : T.IsTree) (ht : 2 ≤ Fintype.card U)
    (G : SimpleGraph V) (hn : 0 < Fintype.card V) (hfree : ¬T.IsContained G) :
    2*G.edgeSet.ncard ≤ (Fintype.card U-2)*Fintype.card V := by
  classical
  let l₀ : List V := Finset.univ.toList
  have hl : l₀.Nodup := Finset.nodup_toList _
  have hlen : l₀.length=Fintype.card V := by simp only [l₀,Finset.length_toList,Finset.card_univ]
  have hne : l₀ ≠ [] := by
    intro he
    have : l₀.length=0 := by rw [he]; rfl
    omega
  have hall : ∀ b, b ∈ l₀ := by intro b; simp only [l₀,Finset.mem_toList,Finset.mem_univ]
  obtain ⟨r⟩ := hT.isConnected.nonempty
  have hb := rooted_word_tree_bound T r hT ht G l₀ hl hne
  rw [rooted_word_count_zero_of_not_contained T r G hfree l₀,Nat.zero_add,
    full_word_base_count G l₀ hl hall,permutationWords_card l₀ hl,hlen] at hb
  have hfact : (Fintype.card V).factorial=Fintype.card V*(Fintype.card V-1).factorial := by
    have he := Nat.factorial_succ (Fintype.card V-1)
    simpa only [Nat.sub_add_cancel hn] using he
  rw [hfact] at hb
  apply Nat.le_of_mul_le_mul_right (c := (Fintype.card V-1).factorial) _ (Nat.factorial_pos _)
  nlinarith only [hb]

end Erdos548

namespace Erdos548

/--
Let $n\geq k+1$. Every graph on $n$ vertices with at least $\frac{k-1}{2}n+1$ edges contains every tree on $k+1$ vertices.
-/
theorem erdos_548 :
    ∀ (n k : ℕ), k + 1 ≤ n → ∀ G : SimpleGraph (Fin n),
      ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ) →
        ∀ T : SimpleGraph (Fin (k + 1)), T.IsTree → T.IsContained G := by
  intro n k hnk G hd T hT
  classical
  have hn : 0<n := by omega
  by_cases hk : k=0
  · subst k
    haveI : Subsingleton (Fin (0+1)) := by change Subsingleton (Fin 1); infer_instance
    let f : Fin (0+1) → Fin n := fun _ => ⟨0,hn⟩
    have hf : Function.Injective f := fun _ _ _ => Subsingleton.elim _ _
    have ha : ∀ {x y}, T.Adj x y → G.Adj (f x) (f y) := by
      intro x y hxy
      exact (hxy.ne (Subsingleton.elim _ _)).elim
    exact ⟨⟨⟨f,ha⟩,hf⟩⟩
  · by_contra hfree
    have hb := tree_free_edge_bound T hT (by simp only [Fintype.card_fin]; omega) G
      (by simpa only [Fintype.card_fin] using hn) hfree
    simp only [Fintype.card_fin] at hb
    have he : k+1-2=k-1 := by omega
    rw [he] at hb
    have hbq : (2:ℚ)*G.edgeSet.ncard ≤ ((k:ℚ)-1)*n := by
      have hh : (k:ℚ)-1=((k-1:ℕ):ℚ) := by
        rw [Nat.cast_sub (by omega)]; norm_num
      rw [hh]
      exact_mod_cast hb
    nlinarith

end Erdos548
