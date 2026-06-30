import BEDC.Derived.PremetricUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.PremetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PremetricCarrier_zero_distance_classifier_boundary [AskSetup] [PackageSetup]
    {X U D Z S M H C Q N uniformRead zeroRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory X ∧ UnaryHistory U ∧ UnaryHistory D ∧ UnaryHistory Z ∧
      UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory H ∧ UnaryHistory C ∧
        UnaryHistory Q ∧ UnaryHistory N ∧ PkgSig bundle Q pkg ∧ PkgSig bundle N pkg →
      Cont X U uniformRead →
        Cont D Z zeroRead →
          Cont zeroRead S completionRead →
            PkgSig bundle completionRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row X ∨ hsame row U ∨ hsame row D ∨ hsame row Z ∨
                      hsame row S ∨ hsame row M ∨ hsame row H ∨ hsame row C ∨
                        hsame row Q ∨ hsame row N ∨ hsame row completionRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont D Z zeroRead ∧
                      Cont zeroRead S completionRead ∧ PkgSig bundle completionRead pkg)
                  hsame ∧
                UnaryHistory zeroRead ∧ UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: PremetricUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier _uniformRoute zeroRoute completionRoute completionPkg
  obtain ⟨_xUnary, _uUnary, dUnary, zUnary, sUnary, _mUnary, _hUnary, _cUnary,
    _qUnary, _nUnary, _qPkg, _nPkg⟩ := carrier
  have zeroUnary : UnaryHistory zeroRead :=
    unary_cont_closed dUnary zUnary zeroRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed zeroUnary sUnary completionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row U ∨ hsame row D ∨ hsame row Z ∨ hsame row S ∨
              hsame row M ∨ hsame row H ∨ hsame row C ∨ hsame row Q ∨ hsame row N ∨
                hsame row completionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D Z zeroRead ∧ Cont zeroRead S completionRead ∧
              PkgSig bundle completionRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro completionRead ⟨hsame_refl completionRead, completionUnary⟩
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, zeroRoute, completionRoute, completionPkg⟩
  }
  exact ⟨cert, zeroUnary, completionUnary⟩

end BEDC.Derived.PremetricUp
