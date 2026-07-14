import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Core
import AnyLayerIdentifiabilityProof.NLayer.KHead.Step2.Trichotomy

set_option autoImplicit false

namespace TransformerIdentifiability.NLayer.NoSkip

/-!
# Model-neutral Step 2 processing order

The deeper-head indices, their lexicographic processing order, and label update
bookkeeping do not depend on whether a transformer layer has a skip connection.
This file gives that neutral KHead scaffold stable NoSkip names.  The analytic
tuple-dial predicates and processing invariant are added only after NS119.
-/

abbrev TrichotomyLabel := KHead.TrichotomyLabel

namespace TrichotomyLabel

abbrev eval {α : Type*} (zeroValue oneValue alphaValue : α) : TrichotomyLabel → α :=
  KHead.TrichotomyLabel.eval zeroValue oneValue alphaValue

@[simp] theorem eval_zero {α : Type*} (zeroValue oneValue alphaValue : α) :
    eval zeroValue oneValue alphaValue KHead.TrichotomyLabel.zero = zeroValue :=
  KHead.TrichotomyLabel.eval_zero zeroValue oneValue alphaValue

@[simp] theorem eval_one {α : Type*} (zeroValue oneValue alphaValue : α) :
    eval zeroValue oneValue alphaValue KHead.TrichotomyLabel.one = oneValue :=
  KHead.TrichotomyLabel.eval_one zeroValue oneValue alphaValue

@[simp] theorem eval_alpha {α : Type*} (zeroValue oneValue alphaValue : α) :
    eval zeroValue oneValue alphaValue KHead.TrichotomyLabel.alpha = alphaValue :=
  KHead.TrichotomyLabel.eval_alpha zeroValue oneValue alphaValue

end TrichotomyLabel

abbrev DeeperHead := KHead.DeeperHead
abbrev IsDeeperHead := KHead.IsDeeperHead
abbrev deeperHeadCount := KHead.deeperHeadCount
abbrev deeperHeadOrder := KHead.deeperHeadOrder

theorem deeperHeadOrder_length (L k : Nat) :
    (deeperHeadOrder L k).length = deeperHeadCount L k :=
  KHead.deeperHeadOrder_length L k

theorem mem_deeperHeadOrder_iff {L k : Nat} {h : DeeperHead} :
    h ∈ deeperHeadOrder L k ↔ IsDeeperHead L k h :=
  KHead.mem_deeperHeadOrder_iff

theorem mk_mem_deeperHeadOrder {L k layer head : Nat}
    (hlow : 2 ≤ layer) (hle : layer ≤ L)
    (hhlo : 1 ≤ head) (hhle : head ≤ k) :
    ({ layer := layer, head := head } : DeeperHead) ∈ deeperHeadOrder L k :=
  KHead.mk_mem_deeperHeadOrder hlow hle hhlo hhle

theorem succ_head_mem_deeperHeadOrder {m k n : Nat} (hnpos : 1 ≤ n)
    (hn : n < m + 1) (a : Fin k) :
    ({ layer := n + 1, head := (a : Nat) + 1 } : DeeperHead) ∈
      deeperHeadOrder (m + 1) k :=
  KHead.succ_head_mem_deeperHeadOrder hnpos hn a

abbrev processedPrefix := KHead.processedPrefix

theorem mem_order_of_mem_processedPrefix {order : List DeeperHead} {n : Nat}
    {h : DeeperHead} (hh : h ∈ processedPrefix order n) : h ∈ order :=
  KHead.mem_order_of_mem_processedPrefix hh

theorem getElem_not_mem_processedPrefix_of_nodup {order : List DeeperHead}
    (hnodup : order.Nodup) {n : Nat} (hn : n < order.length) :
    order[n] ∉ processedPrefix order n :=
  KHead.getElem_not_mem_processedPrefix_of_nodup hnodup hn

abbrev setLabel := KHead.setLabel

@[simp] theorem setLabel_self (labels : DeeperHead → TrichotomyLabel) (h : DeeperHead)
    (label : TrichotomyLabel) : setLabel labels h label h = label :=
  KHead.setLabel_self labels h label

theorem setLabel_of_ne (labels : DeeperHead → TrichotomyLabel) {h g : DeeperHead}
    (label : TrichotomyLabel) (hne : g ≠ h) :
    setLabel labels h label g = labels g :=
  KHead.setLabel_of_ne labels label hne

theorem setLabel_eq_on_processedPrefix_of_not_mem {order : List DeeperHead} {n : Nat}
    (labels : DeeperHead → TrichotomyLabel) {h g : DeeperHead}
    (label : TrichotomyLabel) (hg : g ∈ processedPrefix order n)
    (hh : h ∉ processedPrefix order n) :
    setLabel labels h label g = labels g :=
  KHead.setLabel_eq_on_processedPrefix_of_not_mem labels label hg hh

theorem setLabel_eq_on_processedPrefix_of_getElem_nodup {order : List DeeperHead}
    (hnodup : order.Nodup) (labels : DeeperHead → TrichotomyLabel)
    {n : Nat} (hn : n < order.length) {g : DeeperHead}
    (label : TrichotomyLabel) (hg : g ∈ processedPrefix order n) :
    setLabel labels order[n] label g = labels g :=
  KHead.setLabel_eq_on_processedPrefix_of_getElem_nodup hnodup labels hn label hg

end TransformerIdentifiability.NLayer.NoSkip
