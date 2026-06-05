import BEDC.Derived.BishopRegularCauchyCompletionUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.BishopRegularCauchyCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BishopRegularCauchyCompletionWindowInduction [AskSetup] [PackageSetup]
    {endpoint stream regular dyadic window transport replay provenance name baseRead stepRead
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BishopRegularCauchyCompletionCarrier endpoint stream regular dyadic window transport replay
        provenance name bundle pkg ->
      Cont dyadic window baseRead ->
        Cont baseRead stream stepRead ->
          Cont stepRead regular sealRead ->
            PkgSig bundle sealRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row dyadic ∨ hsame row window ∨ hsame row stream ∨
                      hsame row regular ∨ hsame row sealRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont dyadic window baseRead ∧
                      Cont baseRead stream stepRead ∧ Cont stepRead regular sealRead ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle sealRead pkg)
                  hsame ∧
                UnaryHistory baseRead ∧ UnaryHistory stepRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BishopRegularCauchyCompletionCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier dyadicWindow baseStream stepRegular sealPkg
  obtain ⟨_endpointUnary, streamUnary, regularUnary, dyadicUnary, windowUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, provenancePkg,
    _namePkg⟩ := carrier
  have baseReadUnary : UnaryHistory baseRead :=
    unary_cont_closed dyadicUnary windowUnary dyadicWindow
  have stepReadUnary : UnaryHistory stepRead :=
    unary_cont_closed baseReadUnary streamUnary baseStream
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed stepReadUnary regularUnary stepRegular
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row window ∨ hsame row stream ∨
              hsame row regular ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont dyadic window baseRead ∧
              Cont baseRead stream stepRead ∧ Cont stepRead regular sealRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead
        ⟨hsame_refl sealRead, sealReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, dyadicWindow, baseStream, stepRegular, provenancePkg, sealPkg⟩
  }
  exact ⟨cert, baseReadUnary, stepReadUnary, sealReadUnary⟩

end BEDC.Derived.BishopRegularCauchyCompletionUp
