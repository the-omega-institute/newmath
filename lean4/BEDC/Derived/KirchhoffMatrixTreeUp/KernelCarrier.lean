import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.KirchhoffMatrixTreeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def KirchhoffMatrixTreeCarrier [AskSetup] [PackageSetup]
    (G E L M D S T H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory G ∧ UnaryHistory E ∧ UnaryHistory L ∧ UnaryHistory M ∧
    UnaryHistory D ∧ UnaryHistory S ∧ UnaryHistory T ∧ UnaryHistory H ∧
      UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
        PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem KirchhoffMatrixTreeNameCertObligations [AskSetup] [PackageSetup]
    {G E L M D S T H C P N lapRead detRead treeRead nameRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KirchhoffMatrixTreeCarrier G E L M D S T H C P N bundle pkg →
      Cont G E lapRead →
        Cont lapRead M detRead →
          Cont G S treeRead →
            Cont C N nameRead →
              PkgSig bundle nameRead pkg →
                SemanticNameCert
                    (fun row : BHist =>
                      KirchhoffMatrixTreeCarrier G E L M D S T H C P N bundle pkg ∧
                        hsame row nameRead)
                    (fun row : BHist =>
                      hsame row G ∨ hsame row E ∨ hsame row L ∨ hsame row M ∨
                        hsame row D ∨ hsame row S ∨ hsame row T ∨ hsame row lapRead ∨
                          hsame row detRead ∨ hsame row treeRead ∨ hsame row nameRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont G E lapRead ∧ Cont lapRead M detRead ∧
                        Cont G S treeRead ∧ Cont C N nameRead ∧
                          PkgSig bundle nameRead pkg)
                    hsame ∧
                  UnaryHistory lapRead ∧ UnaryHistory detRead ∧ UnaryHistory treeRead ∧
                    UnaryHistory nameRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier lapRoute detRoute treeRoute nameRoute namePkg
  have carrierFull : KirchhoffMatrixTreeCarrier G E L M D S T H C P N bundle pkg := carrier
  obtain ⟨gUnary, eUnary, _lUnary, mUnary, _dUnary, sUnary, _tUnary, _hUnary,
    cUnary, _pUnary, nUnary, _provenancePkg, _carrierNamePkg⟩ := carrier
  have lapUnary : UnaryHistory lapRead :=
    unary_cont_closed gUnary eUnary lapRoute
  have detUnary : UnaryHistory detRead :=
    unary_cont_closed lapUnary mUnary detRoute
  have treeUnary : UnaryHistory treeRead :=
    unary_cont_closed gUnary sUnary treeRoute
  have nameUnary : UnaryHistory nameRead :=
    unary_cont_closed cUnary nUnary nameRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            KirchhoffMatrixTreeCarrier G E L M D S T H C P N bundle pkg ∧
              hsame row nameRead)
          (fun row : BHist =>
            hsame row G ∨ hsame row E ∨ hsame row L ∨ hsame row M ∨ hsame row D ∨
              hsame row S ∨ hsame row T ∨ hsame row lapRead ∨ hsame row detRead ∨
                hsame row treeRead ∨ hsame row nameRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont G E lapRead ∧ Cont lapRead M detRead ∧
              Cont G S treeRead ∧ Cont C N nameRead ∧ PkgSig bundle nameRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro nameRead ⟨carrierFull, hsame_refl nameRead⟩
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
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
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
                    (Or.inr
                      (Or.inr (Or.inr (Or.inr source.right)))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨unary_transport_symm nameUnary source.right, lapRoute, detRoute, treeRoute,
          nameRoute, namePkg⟩
  }
  exact ⟨cert, lapUnary, detUnary, treeUnary, nameUnary⟩

theorem KirchhoffMatrixTree_laplacian_minor_route [AskSetup] [PackageSetup]
    {G E L M D S T H C P N lapRead minorRead detRead spanRead treeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KirchhoffMatrixTreeCarrier G E L M D S T H C P N bundle pkg ->
      Cont G E lapRead ->
        Cont lapRead L minorRead ->
          Cont minorRead D detRead ->
            Cont G S spanRead ->
              Cont spanRead T treeRead ->
                UnaryHistory detRead ∧ UnaryHistory treeRead ∧ hsame G G := by
  -- BEDC touchpoint anchor: KirchhoffMatrixTreeCarrier BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier lapRoute minorRoute detRoute spanRoute treeRoute
  obtain ⟨gUnary, eUnary, lUnary, _mUnary, dUnary, sUnary, tUnary, _hUnary,
    _cUnary, _pUnary, _nUnary, _provenancePkg, _namePkg⟩ := carrier
  have lapUnary : UnaryHistory lapRead :=
    unary_cont_closed gUnary eUnary lapRoute
  have minorUnary : UnaryHistory minorRead :=
    unary_cont_closed lapUnary lUnary minorRoute
  have detUnary : UnaryHistory detRead :=
    unary_cont_closed minorUnary dUnary detRoute
  have spanUnary : UnaryHistory spanRead :=
    unary_cont_closed gUnary sUnary spanRoute
  have treeUnary : UnaryHistory treeRead :=
    unary_cont_closed spanUnary tUnary treeRoute
  exact ⟨detUnary, treeUnary, hsame_refl G⟩

end BEDC.Derived.KirchhoffMatrixTreeUp
