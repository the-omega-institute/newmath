import BEDC.Derived.DyadicUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.DyadicUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicUpCommonWindowTailEnvelope [AskSetup] [PackageSetup]
    {source exponent mantissa streamWindow regseqRead dyadicRead historyRow classifierRow
      tailRead envelopeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicCarrier source exponent mantissa streamWindow regseqRead dyadicRead historyRow
        classifierRow bundle pkg →
      Cont source streamWindow tailRead →
        Cont tailRead dyadicRead envelopeRead →
          PkgSig bundle envelopeRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row envelopeRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row source ∨ hsame row exponent ∨ hsame row mantissa ∨
                    hsame row streamWindow ∨ hsame row regseqRead ∨ hsame row dyadicRead ∨
                      hsame row tailRead ∨ hsame row envelopeRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont source streamWindow tailRead ∧
                    Cont tailRead dyadicRead envelopeRead ∧ PkgSig bundle envelopeRead pkg)
                hsame ∧ UnaryHistory tailRead ∧ UnaryHistory envelopeRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier tailRoute envelopeRoute envelopePkg
  obtain ⟨sourceUnary, _exponentUnary, _mantissaUnary, streamWindowUnary,
    _regseqReadUnary, dyadicReadUnary, _historyUnary, _classifierUnary,
    _sourceExponentMantissa, _mantissaStreamDyadic, _provenancePkg, _localNamePkg⟩ :=
    carrier
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed sourceUnary streamWindowUnary tailRoute
  have envelopeReadUnary : UnaryHistory envelopeRead :=
    unary_cont_closed tailReadUnary dyadicReadUnary envelopeRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row envelopeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row exponent ∨ hsame row mantissa ∨
              hsame row streamWindow ∨ hsame row regseqRead ∨ hsame row dyadicRead ∨
                hsame row tailRead ∨ hsame row envelopeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont source streamWindow tailRead ∧
              Cont tailRead dyadicRead envelopeRead ∧ PkgSig bundle envelopeRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro envelopeRead ⟨hsame_refl envelopeRead, envelopeReadUnary⟩
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
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, tailRoute, envelopeRoute, envelopePkg⟩
  }
  exact ⟨cert, tailReadUnary, envelopeReadUnary⟩

end BEDC.Derived.DyadicUp
