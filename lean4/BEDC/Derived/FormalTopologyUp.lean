import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FormalTopologyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FormalTopologyCarrier [AskSetup] [PackageSetup]
    (site cover rounded transport route provenance nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory site ∧ UnaryHistory cover ∧ UnaryHistory rounded ∧
    UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
      UnaryHistory nameRow ∧ Cont transport route provenance ∧ PkgSig bundle nameRow pkg

theorem FormalTopologyNameCertObligations [AskSetup] [PackageSetup]
    {site cover rounded transport route provenance nameRow coverRead roundedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FormalTopologyCarrier site cover rounded transport route provenance nameRow bundle pkg ->
      Cont site cover coverRead ->
        Cont coverRead rounded roundedRead ->
          PkgSig bundle roundedRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row roundedRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row site ∨ hsame row cover ∨ hsame row rounded ∨
                    hsame row coverRead ∨ hsame row roundedRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont site cover coverRead ∧
                    Cont coverRead rounded roundedRead ∧ PkgSig bundle roundedRead pkg)
                hsame ∧
              UnaryHistory coverRead ∧ UnaryHistory roundedRead := by
  -- BEDC touchpoint anchor: BHist Cont Pkg NameCert SemanticNameCert
  intro carrier coverRoute roundedRoute roundedPkg
  obtain ⟨siteUnary, coverUnary, roundedUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameUnary, _provenanceRoute, _namePkg⟩ := carrier
  have coverReadUnary : UnaryHistory coverRead :=
    unary_cont_closed siteUnary coverUnary coverRoute
  have roundedReadUnary : UnaryHistory roundedRead :=
    unary_cont_closed coverReadUnary roundedUnary roundedRoute
  have sourceRoundedRead :
      (fun row : BHist => hsame row roundedRead ∧ UnaryHistory row) roundedRead := by
    exact ⟨hsame_refl roundedRead, roundedReadUnary⟩
  have core :
      NameCert
        (fun row : BHist => hsame row roundedRead ∧ UnaryHistory row)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro roundedRead sourceRoundedRead
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _other _third sameRO sameOT
        exact hsame_trans sameRO sameOT
      carrier_respects_equiv := by
        intro _row _other same source
        have sameOtherRounded : hsame _other roundedRead :=
          hsame_trans (hsame_symm same) source.left
        have otherUnary : UnaryHistory _other :=
          unary_transport source.right same
        exact ⟨sameOtherRounded, otherUnary⟩
    }
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row roundedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row site ∨ hsame row cover ∨ hsame row rounded ∨
              hsame row coverRead ∨ hsame row roundedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont site cover coverRead ∧
              Cont coverRead rounded roundedRead ∧ PkgSig bundle roundedRead pkg)
          hsame := by
    exact {
      core := core
      pattern_sound := by
        intro row source
        exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
      ledger_sound := by
        intro row source
        exact ⟨source.right, coverRoute, roundedRoute, roundedPkg⟩
    }
  exact ⟨cert, coverReadUnary, roundedReadUnary⟩

end BEDC.Derived.FormalTopologyUp
