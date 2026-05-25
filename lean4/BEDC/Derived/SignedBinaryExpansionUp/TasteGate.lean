import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary

namespace BEDC.Derived.SignedBinaryExpansionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SignedBinaryExpansionCarrier [AskSetup] [PackageSetup]
    (Q B U D W E Y R L H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  UnaryHistory Q ∧ UnaryHistory B ∧ UnaryHistory U ∧ UnaryHistory D ∧
    UnaryHistory W ∧ UnaryHistory E ∧ UnaryHistory Y ∧ UnaryHistory R ∧
      UnaryHistory L ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
        UnaryHistory N ∧ hsame H (append C W) ∧ PkgSig bundle P pkg

theorem SignedBinaryExpansionCarrier_real_readback_boundary [AskSetup] [PackageSetup]
    {Q B U D W E Y R L H C P N readback sealRead terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SignedBinaryExpansionCarrier Q B U D W E Y R L H C P N bundle pkg →
      Cont E Y readback →
        Cont readback R sealRead →
          Cont sealRead L terminal →
            UnaryHistory readback ∧ UnaryHistory sealRead ∧ UnaryHistory terminal ∧
              hsame H (append C W) ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier enclosureRoute regularRoute terminalRoute
  obtain ⟨_qUnary, _bUnary, _uUnary, _dUnary, _wUnary, eUnary, yUnary, rUnary, lUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, transportRow, provenance⟩ := carrier
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed eUnary yUnary enclosureRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary rUnary regularRoute
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed sealReadUnary lUnary terminalRoute
  exact ⟨readbackUnary, sealReadUnary, terminalUnary, transportRow, provenance⟩

end BEDC.Derived.SignedBinaryExpansionUp
