import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LuenbergerObserverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LuenbergerObserverCarrier [AskSetup] [PackageSetup]
    (A C Y G R E H T P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig
  UnaryHistory A ∧ UnaryHistory C ∧ UnaryHistory Y ∧ UnaryHistory G ∧
    UnaryHistory R ∧ UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory T ∧
      UnaryHistory P ∧ UnaryHistory N ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem LuenbergerObserverCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {A C Y G R E H T P N outputRead errorRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LuenbergerObserverCarrier A C Y G R E H T P N bundle pkg ->
      Cont C Y outputRead ->
        Cont R E errorRead ->
          PkgSig bundle P pkg ->
            PkgSig bundle N pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row outputRead ∨ hsame row errorRead)
                  (fun row : BHist =>
                    hsame row A ∨ hsame row C ∨ hsame row Y ∨ hsame row G ∨
                      hsame row R ∨ hsame row E ∨ hsame row H ∨ hsame row T ∨
                        hsame row P ∨ hsame row N ∨ hsame row outputRead ∨
                          hsame row errorRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                  hsame ∧
                UnaryHistory outputRead ∧ UnaryHistory errorRead := by
  -- BEDC touchpoint anchor: LuenbergerObserverCarrier BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier outputRoute errorRoute pkgP pkgN
  obtain ⟨_aUnary, cUnary, yUnary, _gUnary, rUnary, eUnary, _hUnary, _tUnary,
    _pUnary, _nUnary, _storedP, _storedN⟩ := carrier
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed cUnary yUnary outputRoute
  have errorUnary : UnaryHistory errorRead :=
    unary_cont_closed rUnary eUnary errorRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row outputRead ∨ hsame row errorRead)
          (fun row : BHist =>
            hsame row A ∨ hsame row C ∨ hsame row Y ∨ hsame row G ∨
              hsame row R ∨ hsame row E ∨ hsame row H ∨ hsame row T ∨
                hsame row P ∨ hsame row N ∨ hsame row outputRead ∨
                  hsame row errorRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro outputRead (Or.inl (hsame_refl outputRead))
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
        cases source with
        | inl outputSame =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) outputSame)
        | inr errorSame =>
            exact Or.inr (hsame_trans (hsame_symm sameRows) errorSame)
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl outputSame =>
          right
          right
          right
          right
          right
          right
          right
          right
          right
          right
          exact Or.inl outputSame
      | inr errorSame =>
          right
          right
          right
          right
          right
          right
          right
          right
          right
          right
          exact Or.inr errorSame
    ledger_sound := by
      intro _row source
      cases source with
      | inl outputSame =>
          exact ⟨unary_transport outputUnary (hsame_symm outputSame), pkgP, pkgN⟩
      | inr errorSame =>
          exact ⟨unary_transport errorUnary (hsame_symm errorSame), pkgP, pkgN⟩
  }
  exact ⟨cert, outputUnary, errorUnary⟩

end BEDC.Derived.LuenbergerObserverUp
