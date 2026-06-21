import BEDC.Derived.CompletionExtractorUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CompletionExtractorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompletionExtractorRegularReadbackRoute [AskSetup] [PackageSetup]
    {G M S D Q E H C P N modulusRead windowRead dyadicRead regularRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory G ->
      UnaryHistory M ->
        UnaryHistory S ->
          UnaryHistory D ->
            UnaryHistory Q ->
              UnaryHistory E ->
                Cont G M modulusRead ->
                  Cont modulusRead S windowRead ->
                    Cont windowRead D dyadicRead ->
                      Cont dyadicRead Q regularRead ->
                        Cont regularRead E sealRead ->
                          PkgSig bundle N pkg ->
                            (exists packet : CompletionExtractorUp,
                              packet = CompletionExtractorUp.mk G M S D Q E H C P N) ∧
                              SemanticNameCert
                                (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row G ∨ hsame row M ∨ hsame row S ∨
                                    hsame row D ∨ hsame row Q ∨ hsame row E ∨
                                      hsame row sealRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont G M modulusRead ∧
                                    Cont modulusRead S windowRead ∧
                                      Cont windowRead D dyadicRead ∧
                                        Cont dyadicRead Q regularRead ∧
                                          Cont regularRead E sealRead ∧
                                            PkgSig bundle N pkg)
                                hsame ∧
                                UnaryHistory modulusRead ∧ UnaryHistory windowRead ∧
                                  UnaryHistory dyadicRead ∧ UnaryHistory regularRead ∧
                                    UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro gUnary mUnary sUnary dUnary qUnary eUnary modulusRoute windowRoute dyadicRoute
    regularRoute sealRoute namePkg
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed gUnary mUnary modulusRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed modulusUnary sUnary windowRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed windowUnary dUnary dyadicRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed dyadicUnary qUnary regularRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed regularUnary eUnary sealRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row G ∨ hsame row M ∨ hsame row S ∨ hsame row D ∨ hsame row Q ∨
            hsame row E ∨ hsame row sealRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont G M modulusRead ∧ Cont modulusRead S windowRead ∧
            Cont windowRead D dyadicRead ∧ Cont dyadicRead Q regularRead ∧
              Cont regularRead E sealRead ∧ PkgSig bundle N pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, modulusRoute, windowRoute, dyadicRoute, regularRoute, sealRoute,
          namePkg⟩
  }
  exact
    ⟨Exists.intro (CompletionExtractorUp.mk G M S D Q E H C P N) rfl, cert,
      modulusUnary, windowUnary, dyadicUnary, regularUnary, sealUnary⟩

end BEDC.Derived.CompletionExtractorUp
