import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyAbsUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyAbsCarrier_public_export_surface [AskSetup] [PackageSetup]
    {source windows endpoints absRows readback sealRow transport replay provenance localName
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory source ∧ UnaryHistory windows ∧ UnaryHistory endpoints ∧
        UnaryHistory absRows ∧ UnaryHistory readback ∧ UnaryHistory sealRow ∧
          UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
            UnaryHistory localName ∧ PkgSig bundle provenance pkg →
      Cont source windows endpoints →
        Cont endpoints absRows readback →
          Cont readback sealRow publicRead →
            PkgSig bundle publicRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row source ∨ hsame row windows ∨ hsame row endpoints ∨
                      hsame row absRows ∨ hsame row readback ∨ hsame row sealRow ∨
                        hsame row publicRead)
                  (fun row : BHist => UnaryHistory row ∧ PkgSig bundle publicRead pkg)
                  hsame ∧
                UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro carrier sourceWindowsRoute endpointAbsRoute readbackSealRoute publicPkg
  obtain ⟨sourceUnary, windowsUnary, endpointsUnary, absRowsUnary, _readbackUnary,
    sealRowUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _provenancePkg⟩ := carrier
  have endpointsRouteUnary : UnaryHistory endpoints :=
    unary_cont_closed sourceUnary windowsUnary sourceWindowsRoute
  have readbackRouteUnary : UnaryHistory readback :=
    unary_cont_closed endpointsRouteUnary absRowsUnary endpointAbsRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed readbackRouteUnary sealRowUnary readbackSealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row windows ∨ hsame row endpoints ∨
              hsame row absRows ∨ hsame row readback ∨ hsame row sealRow ∨
                hsame row publicRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr sourceRow.left)))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, publicPkg⟩
  }
  exact ⟨cert, publicUnary⟩

end BEDC.Derived.RegularCauchyAbsUp
