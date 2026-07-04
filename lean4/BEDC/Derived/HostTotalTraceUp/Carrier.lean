import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.HostTotalTraceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def HostTotalTraceCarrier [AskSetup] [PackageSetup]
    (H F R E U L C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory H ∧ UnaryHistory F ∧ UnaryHistory R ∧ UnaryHistory E ∧
    UnaryHistory U ∧ UnaryHistory L ∧ UnaryHistory C ∧ UnaryHistory P ∧
      UnaryHistory N ∧ Cont H F R ∧ Cont F R E ∧ Cont F E U ∧ Cont L C N ∧
        PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem HostTotalTraceCarrier_name_route_projection [AskSetup] [PackageSetup]
    {H F R E U L C P N routeRead : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HostTotalTraceCarrier H F R E U L C P N bundle pkg →
      Cont C N routeRead →
        PkgSig bundle routeRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row H ∨ hsame row F ∨ hsame row R ∨ hsame row E ∨ hsame row U ∨
                  hsame row L ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                    hsame row routeRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont L C N ∧ Cont C N routeRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
                    PkgSig bundle routeRead pkg)
              hsame ∧ UnaryHistory routeRead := by
  -- BEDC touchpoint anchor: HostTotalTraceCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier routeCont routePkg
  obtain ⟨_hostUnary, _fuelUnary, _readbackUnary, _endpointUnary, _timeoutUnary,
    _transportUnary, routeUnary, _provenanceUnary, nameUnary, _hostFuelReadback,
    _fuelReadbackEndpoint, _fuelEndpointTimeout, transportRouteName, provenancePkg,
    namePkg⟩ := carrier
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed routeUnary nameUnary routeCont
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row H ∨ hsame row F ∨ hsame row R ∨ hsame row E ∨ hsame row U ∨
              hsame row L ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row routeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont L C N ∧ Cont C N routeRead ∧
              PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧ PkgSig bundle routeRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro routeRead
        ⟨hsame_refl routeRead, routeReadUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, transportRouteName, routeCont, provenancePkg, namePkg, routePkg⟩
  }
  exact ⟨cert, routeReadUnary⟩

end BEDC.Derived.HostTotalTraceUp
