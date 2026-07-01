import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Package
import BEDC.Derived.CircleUp.TasteGate

namespace BEDC.Derived.CircleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CircleCarrier [AskSetup] [PackageSetup]
    (boundary real metric compact sone transport provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory boundary ∧ UnaryHistory real ∧ UnaryHistory metric ∧
    UnaryHistory compact ∧ UnaryHistory sone ∧ UnaryHistory transport ∧
      UnaryHistory provenance ∧ UnaryHistory localName ∧ PkgSig bundle provenance pkg

theorem CircleCarrier_public_boundary_export [AskSetup] [PackageSetup]
    {boundary real metric compact sone transport provenance localName boundaryRead
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CircleCarrier boundary real metric compact sone transport provenance localName bundle pkg →
      Cont boundary real boundaryRead →
        Cont boundaryRead localName publicRead →
          PkgSig bundle publicRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row boundary ∨ hsame row real ∨ hsame row metric ∨
                    hsame row compact ∨ hsame row sone ∨ hsame row transport ∨
                      hsame row provenance ∨ hsame row localName ∨ hsame row publicRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont boundary real boundaryRead ∧
                    Cont boundaryRead localName publicRead ∧ PkgSig bundle publicRead pkg)
                hsame ∧
              UnaryHistory boundaryRead ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: CircleCarrier BHist Cont ProbeBundle PkgSig hsame SemanticNameCert
  intro carrier boundaryRoute publicRoute publicPkg
  obtain ⟨boundaryUnary, realUnary, _metricUnary, _compactUnary, _soneUnary,
    _transportUnary, _provenanceUnary, localNameUnary, _provenancePkg⟩ := carrier
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed boundaryUnary realUnary boundaryRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed boundaryReadUnary localNameUnary publicRoute
  have sourcePublic :
      (fun row : BHist => hsame row publicRead ∧ UnaryHistory row) publicRead := by
    exact ⟨hsame_refl publicRead, publicUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row boundary ∨ hsame row real ∨ hsame row metric ∨
              hsame row compact ∨ hsame row sone ∨ hsame row transport ∨
                hsame row provenance ∨ hsame row localName ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont boundary real boundaryRead ∧
              Cont boundaryRead localName publicRead ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead sourcePublic
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, boundaryRoute, publicRoute, publicPkg⟩
  }
  exact ⟨cert, boundaryReadUnary, publicUnary⟩

end BEDC.Derived.CircleUp
