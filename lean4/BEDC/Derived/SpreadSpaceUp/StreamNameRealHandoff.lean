import BEDC.Derived.SpreadSpaceUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SpreadSpaceUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SpreadSpace_streamname_real_handoff [AskSetup] [PackageSetup]
    {B L Q W R E H C P N prefixRead streamRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory B → UnaryHistory L → UnaryHistory Q → UnaryHistory W → UnaryHistory R →
      Cont B L prefixRead → Cont Q W streamRead → Cont streamRead R realRead →
        PkgSig bundle P pkg →
          UnaryHistory prefixRead ∧ UnaryHistory streamRead ∧ UnaryHistory realRead ∧
            PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro bUnary lUnary qUnary wUnary rUnary prefixRoute streamRoute realRoute provenance
  have _structuralRows :
      hsame E E ∧ hsame H H ∧ hsame C C ∧ hsame N N :=
    ⟨hsame_refl E, hsame_refl H, hsame_refl C, hsame_refl N⟩
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed bUnary lUnary prefixRoute
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed qUnary wUnary streamRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed streamUnary rUnary realRoute
  exact ⟨prefixUnary, streamUnary, realUnary, provenance⟩

end BEDC.Derived.SpreadSpaceUp
