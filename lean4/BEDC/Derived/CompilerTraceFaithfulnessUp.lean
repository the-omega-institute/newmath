import BEDC.FKernel.Hist
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Assoc

namespace BEDC.Derived.CompilerTraceFaithfulnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

def CompilerTraceFaithfulnessCarrier (S T K M G R L H C P N : BHist) : Prop :=
  Cont S G R ∧ Cont R L T ∧ hsame K M ∧ hsame G G ∧ hsame L L ∧ hsame H H ∧
    hsame C C ∧ hsame P N

theorem CompilerTraceFaithfulnessCarrier_source_replay_composite
    {S T K M G R L H C P N : BHist}
    (carrier : CompilerTraceFaithfulnessCarrier S T K M G R L H C P N) :
    Cont S (append G L) T ∧ hsame P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  constructor
  · cases carrier.left
    cases carrier.right.left
    exact append_assoc S G L
  · exact carrier.right.right.right.right.right.right.right

end BEDC.Derived.CompilerTraceFaithfulnessUp
