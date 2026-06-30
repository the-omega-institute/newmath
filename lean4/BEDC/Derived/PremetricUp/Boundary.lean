import BEDC.Derived.PremetricUp.TasteGate
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.PremetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def PremetricCarrier [AskSetup] [PackageSetup]
    (X U D Z S M H C Q N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig UnaryHistory
  UnaryHistory X ∧ UnaryHistory U ∧ UnaryHistory D ∧ UnaryHistory Z ∧
    UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory Q ∧ UnaryHistory N ∧ PkgSig bundle Q pkg ∧ PkgSig bundle N pkg

theorem PremetricZeroDistanceClassifierBoundary [AskSetup] [PackageSetup]
    {X U D Z S M H C Q N zeroRead reflectionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PremetricCarrier X U D Z S M H C Q N bundle pkg →
      Cont D Z zeroRead →
        Cont zeroRead S reflectionRead →
          PkgSig bundle reflectionRead pkg →
            UnaryHistory D ∧ UnaryHistory Z ∧ UnaryHistory zeroRead ∧
              UnaryHistory reflectionRead ∧ Cont D Z zeroRead ∧
                Cont zeroRead S reflectionRead ∧ PkgSig bundle reflectionRead pkg := by
  -- BEDC touchpoint anchor: PremetricCarrier BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier zeroRoute reflectionRoute reflectionPkg
  obtain ⟨_xUnary, _uUnary, dUnary, zUnary, sUnary, _mUnary, _hUnary, _cUnary,
    _qUnary, _nUnary, _qPkg, _nPkg⟩ := carrier
  have zeroUnary : UnaryHistory zeroRead :=
    unary_cont_closed dUnary zUnary zeroRoute
  have reflectionUnary : UnaryHistory reflectionRead :=
    unary_cont_closed zeroUnary sUnary reflectionRoute
  exact
    ⟨dUnary, zUnary, zeroUnary, reflectionUnary, zeroRoute, reflectionRoute, reflectionPkg⟩

theorem PremetricCompletionBoundary [AskSetup] [PackageSetup]
    {X U D Z S M H C Q N completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PremetricCarrier X U D Z S M H C Q N bundle pkg →
      Cont S M completionRead →
        PkgSig bundle completionRead pkg →
          UnaryHistory X ∧ UnaryHistory U ∧ UnaryHistory D ∧ UnaryHistory Z ∧
            UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory completionRead ∧
              Cont S M completionRead ∧ PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: PremetricCarrier BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier completionRoute completionPkg
  obtain ⟨xUnary, uUnary, dUnary, zUnary, sUnary, mUnary, _hUnary, _cUnary,
    _qUnary, _nUnary, _qPkg, _nPkg⟩ := carrier
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed sUnary mUnary completionRoute
  exact
    ⟨xUnary, uUnary, dUnary, zUnary, sUnary, mUnary, completionUnary, completionRoute,
      completionPkg⟩

theorem PremetricCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {X U D Z S M H C Q N uniformRead zeroRead reflectionRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PremetricCarrier X U D Z S M H C Q N bundle pkg →
      Cont X U uniformRead →
        Cont D Z zeroRead →
          Cont zeroRead S reflectionRead →
            Cont reflectionRead M completionRead →
              PkgSig bundle completionRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row X ∨ hsame row U ∨ hsame row D ∨ hsame row Z ∨
                        hsame row S ∨ hsame row M ∨ hsame row H ∨ hsame row C ∨
                          hsame row Q ∨ hsame row N ∨ hsame row completionRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont X U uniformRead ∧ Cont D Z zeroRead ∧
                        Cont zeroRead S reflectionRead ∧
                          Cont reflectionRead M completionRead ∧
                            PkgSig bundle completionRead pkg)
                    hsame ∧ UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: PremetricCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier uniformRoute zeroRoute reflectionRoute completionRoute completionPkg
  obtain ⟨xUnary, uUnary, dUnary, zUnary, sUnary, mUnary, _hUnary, _cUnary, _qUnary,
    _nUnary, _qPkg, _nPkg⟩ := carrier
  have _uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed xUnary uUnary uniformRoute
  have zeroUnary : UnaryHistory zeroRead :=
    unary_cont_closed dUnary zUnary zeroRoute
  have reflectionUnary : UnaryHistory reflectionRead :=
    unary_cont_closed zeroUnary sUnary reflectionRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed reflectionUnary mUnary completionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row U ∨ hsame row D ∨ hsame row Z ∨
              hsame row S ∨ hsame row M ∨ hsame row H ∨ hsame row C ∨
                hsame row Q ∨ hsame row N ∨ hsame row completionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont X U uniformRead ∧ Cont D Z zeroRead ∧
              Cont zeroRead S reflectionRead ∧ Cont reflectionRead M completionRead ∧
                PkgSig bundle completionRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro completionRead
        ⟨hsame_refl completionRead, completionUnary⟩
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
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, uniformRoute, zeroRoute, reflectionRoute, completionRoute,
          completionPkg⟩
  }
  exact ⟨cert, completionUnary⟩

end BEDC.Derived.PremetricUp
