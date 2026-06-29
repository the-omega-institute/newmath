import BEDC.Derived.CanonicalTailChoiceUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CanonicalTailChoiceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CanonicalTailChoiceCarrier [AskSetup] [PackageSetup]
    (M E I T S R H C0 P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig UnaryHistory
  UnaryHistory M ∧ UnaryHistory E ∧ UnaryHistory I ∧ UnaryHistory T ∧
    UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory H ∧ UnaryHistory C0 ∧
      UnaryHistory P ∧ UnaryHistory N ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem CanonicalTailChoiceCarrier_nonescape [AskSetup] [PackageSetup]
    {M E I T S R H C0 P N windowRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CanonicalTailChoiceCarrier M E I T S R H C0 P N bundle pkg →
      Cont M T windowRead →
        Cont windowRead E sealRead →
          PkgSig bundle sealRead pkg →
            SemanticNameCert
              (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row M ∨ hsame row E ∨ hsame row I ∨ hsame row T ∨
                  hsame row S ∨ hsame row R ∨ hsame row H ∨ hsame row C0 ∨
                    hsame row P ∨ hsame row N ∨ hsame row windowRead ∨
                      hsame row sealRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont M T windowRead ∧
                  Cont windowRead E sealRead ∧ PkgSig bundle sealRead pkg)
              hsame ∧ UnaryHistory windowRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier windowRoute sealRoute sealPkg
  obtain ⟨mUnary, eUnary, _iUnary, tUnary, _sUnary, _rUnary, _hUnary, _c0Unary,
    _pUnary, _nUnary, _pPkg, _nPkg⟩ := carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed mUnary tUnary windowRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed windowUnary eUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row E ∨ hsame row I ∨ hsame row T ∨
              hsame row S ∨ hsame row R ∨ hsame row H ∨ hsame row C0 ∨
                hsame row P ∨ hsame row N ∨ hsame row windowRead ∨
                  hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M T windowRead ∧ Cont windowRead E sealRead ∧
              PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
      repeat (first | exact source.left | apply Or.inr)
    ledger_sound := by
      intro _row source
      exact ⟨source.right, windowRoute, sealRoute, sealPkg⟩
  }
  exact ⟨cert, windowUnary, sealUnary⟩

theorem CanonicalTailChoiceCarrier_no_choice_nonescape [AskSetup] [PackageSetup]
    {M E I T S R H C0 P N indexRead tailRead sealRead refusalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CanonicalTailChoiceCarrier M E I T S R H C0 P N bundle pkg →
      Cont M E indexRead →
        Cont indexRead T tailRead →
          Cont tailRead S sealRead →
            Cont sealRead R refusalRead →
              PkgSig bundle refusalRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row M ∨ hsame row E ∨ hsame row I ∨ hsame row T ∨
                        hsame row S ∨ hsame row R ∨ hsame row refusalRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont M E indexRead ∧
                        Cont indexRead T tailRead ∧ Cont tailRead S sealRead ∧
                          Cont sealRead R refusalRead ∧
                            PkgSig bundle refusalRead pkg)
                    hsame ∧ UnaryHistory refusalRead := by
  -- BEDC touchpoint anchor: CanonicalTailChoiceCarrier BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier indexRoute tailRoute sealRoute refusalRoute refusalPkg
  obtain ⟨mUnary, eUnary, _iUnary, tUnary, sUnary, rUnary, _hUnary, _c0Unary,
    _pUnary, _nUnary, _pPkg, _nPkg⟩ := carrier
  have indexUnary : UnaryHistory indexRead :=
    unary_cont_closed mUnary eUnary indexRoute
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed indexUnary tUnary tailRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary sUnary sealRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed sealUnary rUnary refusalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row E ∨ hsame row I ∨ hsame row T ∨
              hsame row S ∨ hsame row R ∨ hsame row refusalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M E indexRead ∧ Cont indexRead T tailRead ∧
              Cont tailRead S sealRead ∧ Cont sealRead R refusalRead ∧
                PkgSig bundle refusalRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro refusalRead ⟨hsame_refl refusalRead, refusalUnary⟩
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
      repeat (first | exact source.left | apply Or.inr)
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, indexRoute, tailRoute, sealRoute, refusalRoute, refusalPkg⟩
  }
  exact ⟨cert, refusalUnary⟩

end BEDC.Derived.CanonicalTailChoiceUp
