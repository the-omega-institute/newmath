import BEDC.Derived.UniformCauchySeriesUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.UniformCauchySeriesUp.TailThreshold

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchySeriesTailThresholdSemanticCertificate [AskSetup] [PackageSetup]
    {term partialSum window readback dyadic threshold endpoint transport replay provenance
      localName tailRead endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory term →
      UnaryHistory partialSum →
        UnaryHistory window →
          UnaryHistory readback →
            UnaryHistory dyadic →
              UnaryHistory threshold →
                UnaryHistory endpoint →
                  Cont term partialSum window →
                    Cont window readback dyadic →
                      Cont dyadic threshold tailRead →
                        Cont tailRead endpoint endpointRead →
                          PkgSig bundle provenance pkg →
                            PkgSig bundle localName pkg →
                              SemanticNameCert
                                  (fun row : BHist =>
                                    (hsame row tailRead ∨ hsame row endpointRead) ∧
                                      UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row term ∨ hsame row partialSum ∨
                                      hsame row window ∨ hsame row readback ∨
                                        hsame row dyadic ∨ hsame row threshold ∨
                                          hsame row endpoint ∨ hsame row tailRead ∨
                                            hsame row endpointRead)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                                      PkgSig bundle localName pkg)
                                  hsame ∧
                                UnaryHistory tailRead ∧ UnaryHistory endpointRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro _termUnary _partialSumUnary _windowUnary _readbackUnary dyadicUnary thresholdUnary
    endpointUnary _windowRoute _dyadicRoute tailRoute endpointRoute provenancePkg localNamePkg
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed dyadicUnary thresholdUnary tailRoute
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed tailUnary endpointUnary endpointRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row tailRead ∨ hsame row endpointRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row term ∨ hsame row partialSum ∨ hsame row window ∨
              hsame row readback ∨ hsame row dyadic ∨ hsame row threshold ∨
                hsame row endpoint ∨ hsame row tailRead ∨ hsame row endpointRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpointRead
        ⟨Or.inr (hsame_refl endpointRead), endpointReadUnary⟩
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
        constructor
        · cases source.left with
          | inl sameTail =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameTail)
          | inr sameEndpoint =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) sameEndpoint)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameTail =>
          right
          right
          right
          right
          right
          right
          right
          exact Or.inl sameTail
      | inr sameEndpoint =>
          right
          right
          right
          right
          right
          right
          right
          exact Or.inr sameEndpoint
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, tailUnary, endpointReadUnary⟩

end BEDC.Derived.UniformCauchySeriesUp.TailThreshold
