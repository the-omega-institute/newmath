import BEDC.Derived.ReflectiveInquiryUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Package

namespace BEDC.Derived.ReflectiveInquiryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem ReflectiveInquiryFieldFaithfulRowSeparation [BEDC.FKernel.Ask.AskSetup] [PackageSetup]
    {P F S K A R L H C Q N bridge audit : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    hsame bridge S →
      hsame audit K →
        Cont P F C →
          PkgSig bundle A pkg →
            P ≠ F →
              Q ≠ H →
                hsame bridge S ∧ hsame audit K ∧ Cont P F C ∧ PkgSig bundle A pkg ∧
                  P ≠ F ∧ Q ≠ H := by
  -- BEDC touchpoint anchor: ReflectiveInquiryUp FieldFaithful BHist Cont ProbeBundle PkgSig hsame
  intro bridgeSame auditSame sourceRoute packageRead sourceSeparated openReplaySeparated
  exact
    ⟨bridgeSame, auditSame, sourceRoute, packageRead, sourceSeparated,
      openReplaySeparated⟩

end BEDC.Derived.ReflectiveInquiryUp
