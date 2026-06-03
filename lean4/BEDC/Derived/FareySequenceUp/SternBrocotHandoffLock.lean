import BEDC.Derived.FareySequenceUp.TasteGate

namespace BEDC.Derived.FareySequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FareySequenceSternBrocotHandoffLock [AskSetup] [PackageSetup]
    {B A M L T S D Q W R G E H C P N boundaryRead mediantRead capRead toleranceRead
      sternRead approxRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FareySequenceCarrier B A M L T S D Q W R G E H C P N bundle pkg ->
      Cont B A boundaryRead ->
        Cont boundaryRead M mediantRead ->
          Cont mediantRead L capRead ->
            Cont capRead T toleranceRead ->
              Cont toleranceRead S sternRead ->
                Cont sternRead G approxRead ->
                  PkgSig bundle approxRead pkg ->
                    SemanticNameCert
                        (fun row : BHist => hsame row approxRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row B ∨ hsame row A ∨ hsame row M ∨ hsame row L ∨
                            hsame row T ∨ hsame row S ∨ hsame row G ∨
                              hsame row boundaryRead ∨ hsame row mediantRead ∨
                                hsame row capRead ∨ hsame row toleranceRead ∨
                                  hsame row sternRead ∨ hsame row approxRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont B A boundaryRead ∧
                            Cont boundaryRead M mediantRead ∧ Cont mediantRead L capRead ∧
                              Cont capRead T toleranceRead ∧ Cont toleranceRead S sternRead ∧
                                Cont sternRead G approxRead ∧ PkgSig bundle approxRead pkg)
                        hsame ∧
                      UnaryHistory boundaryRead ∧ UnaryHistory mediantRead ∧
                        UnaryHistory capRead ∧ UnaryHistory toleranceRead ∧
                          UnaryHistory sternRead ∧ UnaryHistory approxRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier boundaryRoute mediantRoute capRoute toleranceRoute sternRoute approxRoute
    approxPkg
  obtain ⟨bUnary, aUnary, mUnary, lUnary, tUnary, sUnary, _dUnary, _qUnary,
    _wUnary, _rUnary, gUnary, _eUnary, _hUnary, _cUnary, _pUnary, _nUnary,
    _aEmpty, _sEmpty, _mEmpty, _gEmpty, _eEmpty, _provenancePkg⟩ := carrier
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed bUnary aUnary boundaryRoute
  have mediantUnary : UnaryHistory mediantRead :=
    unary_cont_closed boundaryUnary mUnary mediantRoute
  have capUnary : UnaryHistory capRead :=
    unary_cont_closed mediantUnary lUnary capRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed capUnary tUnary toleranceRoute
  have sternUnary : UnaryHistory sternRead :=
    unary_cont_closed toleranceUnary sUnary sternRoute
  have approxUnary : UnaryHistory approxRead :=
    unary_cont_closed sternUnary gUnary approxRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row approxRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row A ∨ hsame row M ∨ hsame row L ∨ hsame row T ∨
              hsame row S ∨ hsame row G ∨ hsame row boundaryRead ∨
                hsame row mediantRead ∨ hsame row capRead ∨ hsame row toleranceRead ∨
                  hsame row sternRead ∨ hsame row approxRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont B A boundaryRead ∧ Cont boundaryRead M mediantRead ∧
              Cont mediantRead L capRead ∧ Cont capRead T toleranceRead ∧
                Cont toleranceRead S sternRead ∧ Cont sternRead G approxRead ∧
                  PkgSig bundle approxRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro approxRead ⟨hsame_refl approxRead, approxUnary⟩
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
        intro _row other sameRows source
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
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, boundaryRoute, mediantRoute, capRoute, toleranceRoute, sternRoute,
          approxRoute, approxPkg⟩
  }
  exact
    ⟨cert, boundaryUnary, mediantUnary, capUnary, toleranceUnary, sternUnary, approxUnary⟩

end BEDC.Derived.FareySequenceUp
