import BEDC.Derived.CalderonZygmundOperatorUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CalderonZygmundOperatorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CalderonZygmundOperatorNameCertObligations [AskSetup] [PackageSetup]
    {X W S A L M D E H C P N kernelRead cancellationRead sealedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory X ->
      UnaryHistory W ->
        UnaryHistory S ->
          UnaryHistory A ->
            UnaryHistory L ->
              UnaryHistory M ->
                UnaryHistory D ->
                  UnaryHistory E ->
                    UnaryHistory C ->
                      UnaryHistory N ->
                        Cont W S kernelRead ->
                          Cont A L cancellationRead ->
                            Cont cancellationRead D sealedRead ->
                              PkgSig bundle sealedRead pkg ->
                                SemanticNameCert
                                    (fun row : BHist => hsame row sealedRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row X ∨ hsame row W ∨ hsame row S ∨ hsame row A ∨
                                        hsame row L ∨ hsame row M ∨ hsame row D ∨ hsame row E ∨
                                          hsame row C ∨ hsame row N ∨ hsame row sealedRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont W S kernelRead ∧
                                        Cont A L cancellationRead ∧
                                          Cont cancellationRead D sealedRead ∧
                                            PkgSig bundle sealedRead pkg)
                                    hsame ∧
                                  UnaryHistory kernelRead ∧ UnaryHistory cancellationRead ∧
                                    UnaryHistory sealedRead ∧ Cont W S kernelRead ∧
                                      Cont A L cancellationRead ∧
                                        Cont cancellationRead D sealedRead ∧
                                          PkgSig bundle sealedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro _sourceUnary windowUnary sizeUnary cancellationUnary localUnary _maximalUnary dyadicUnary
    _realUnary _replayUnary _nameUnary kernelRoute cancellationRoute sealedRoute sealedPkg
  have kernelUnary : UnaryHistory kernelRead :=
    unary_cont_closed windowUnary sizeUnary kernelRoute
  have cancellationReadUnary : UnaryHistory cancellationRead :=
    unary_cont_closed cancellationUnary localUnary cancellationRoute
  have sealedUnary : UnaryHistory sealedRead :=
    unary_cont_closed cancellationReadUnary dyadicUnary sealedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row W ∨ hsame row S ∨ hsame row A ∨ hsame row L ∨
              hsame row M ∨ hsame row D ∨ hsame row E ∨ hsame row C ∨ hsame row N ∨
                hsame row sealedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W S kernelRead ∧ Cont A L cancellationRead ∧
              Cont cancellationRead D sealedRead ∧ PkgSig bundle sealedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealedRead ⟨hsame_refl sealedRead, sealedUnary⟩
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
        exact ⟨hsame_trans (hsame_symm sameRows) source.left,
          unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, kernelRoute, cancellationRoute, sealedRoute, sealedPkg⟩
  }
  exact
    ⟨cert, kernelUnary, cancellationReadUnary, sealedUnary, kernelRoute, cancellationRoute,
      sealedRoute, sealedPkg⟩

end BEDC.Derived.CalderonZygmundOperatorUp
