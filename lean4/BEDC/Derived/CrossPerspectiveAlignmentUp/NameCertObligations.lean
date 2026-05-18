import BEDC.Derived.CrossPerspectiveAlignmentUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CrossPerspectiveAlignmentUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CrossPerspectiveAlignmentCarrier [AskSetup] [PackageSetup]
    (source target locality commitment multiHist transports routes provenance nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory locality ∧
    UnaryHistory commitment ∧ UnaryHistory multiHist ∧ UnaryHistory transports ∧
      UnaryHistory routes ∧ UnaryHistory provenance ∧ UnaryHistory nameCert ∧
        hsame nameCert source ∧ PkgSig bundle provenance pkg

theorem CrossPerspectiveAlignmentCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {source target locality commitment multiHist transports routes provenance nameCert
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CrossPerspectiveAlignmentCarrier source target locality commitment multiHist transports routes
        provenance nameCert bundle pkg →
      Cont source target publicRead →
        PkgSig bundle publicRead pkg →
          UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory locality ∧
            UnaryHistory commitment ∧ UnaryHistory multiHist ∧ UnaryHistory publicRead ∧
              SemanticNameCert
                (fun row : BHist =>
                  CrossPerspectiveAlignmentCarrier source target locality commitment multiHist
                    transports routes provenance nameCert bundle pkg ∧ hsame row nameCert)
                (fun row : BHist =>
                  hsame row source ∨ hsame row target ∨ hsame row locality ∨
                    hsame row commitment ∨ hsame row multiHist ∨ hsame row publicRead)
                (fun row : BHist =>
                  PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg ∧
                    hsame row nameCert)
                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier sourceTargetPublic publicPkg
  have carrierPacket :
      CrossPerspectiveAlignmentCarrier source target locality commitment multiHist transports
        routes provenance nameCert bundle pkg :=
    carrier
  obtain ⟨sourceUnary, targetUnary, localityUnary, commitmentUnary, multiHistUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, nameCertUnary, nameCertSameSource,
    provenancePkg⟩ := carrier
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed sourceUnary targetUnary sourceTargetPublic
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          CrossPerspectiveAlignmentCarrier source target locality commitment multiHist
            transports routes provenance nameCert bundle pkg ∧ hsame row nameCert)
        (fun row : BHist =>
          hsame row source ∨ hsame row target ∨ hsame row locality ∨
            hsame row commitment ∨ hsame row multiHist ∨ hsame row publicRead)
        (fun row : BHist =>
          PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg ∧
            hsame row nameCert)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro nameCert ⟨carrierPacket, hsame_refl nameCert⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same sourceRow
          exact ⟨sourceRow.left, hsame_trans (hsame_symm same) sourceRow.right⟩
      }
      pattern_sound := by
        intro _row sourceRow
        exact Or.inl (hsame_trans sourceRow.right nameCertSameSource)
      ledger_sound := by
        intro _row sourceRow
        exact ⟨provenancePkg, publicPkg, sourceRow.right⟩
    }
  exact
    ⟨sourceUnary, targetUnary, localityUnary, commitmentUnary, multiHistUnary, publicUnary,
      cert⟩

end BEDC.Derived.CrossPerspectiveAlignmentUp
