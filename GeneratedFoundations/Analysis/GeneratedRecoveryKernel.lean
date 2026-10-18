module

public import GeneratedFoundations.Analysis.HistoryFrontier
public import GeneratedFoundations.Analysis.FinitePoissonOverlap
public import GeneratedFoundations.Analysis.HistoryTiltedBalance

/-!
# Finite generated recovery kernel

This entry assembles the finite, source-internal statements selected from the
generated-world recovery analysis:

* deterministic minimal-frontier evaluation of complete histories;
* the order-two falling-factorial overlap algebra and its fixed constants;
* exact doubled-tilt balance on every actual merge/split edge.

The package introduces no new datum and no custom axiom.  It is the finite
algebraic and combinatorial kernel used by later scale-uniform analysis; it is
not a replacement for the analytic context summation or limiting argument.
-/

@[expose] public section

namespace GeneratedFoundations.Analysis.GeneratedRecoveryKernel

structure Conclusions : Prop where
  frontier : HistoryFrontier.Conclusions
  local_overlap : FinitePoissonOverlap.Conclusions
  bottom_edge : HistoryTiltedBalance.Conclusions

theorem generatedRecoveryKernelConclusions : Conclusions where
  frontier := HistoryFrontier.historyFrontierConclusions
  local_overlap := FinitePoissonOverlap.finitePoissonOverlapConclusions
  bottom_edge := HistoryTiltedBalance.historyTiltedBalanceConclusions

end GeneratedFoundations.Analysis.GeneratedRecoveryKernel
