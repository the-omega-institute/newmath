import BEDC.Derived.RegularCauchyRingUp

namespace BEDC.Derived.RegularCauchyRingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyRingScopedKernelDependency [AskSetup] [PackageSetup]
    {A B WA WB DA DB S G M L RS RG RM RL ES EG EM EL H C P N additiveRead
      multiplicativeRead scopedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyRingCarrier A B WA WB DA DB S G M L RS RG RM RL ES EG EM EL H C P N
        bundle pkg →
      Cont S G additiveRead →
        Cont M L multiplicativeRead →
          Cont additiveRead multiplicativeRead scopedRead →
            PkgSig bundle scopedRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row A ∨ hsame row B ∨ hsame row WA ∨ hsame row WB ∨
                      hsame row DA ∨ hsame row DB ∨ hsame row S ∨ hsame row G ∨
                        hsame row M ∨ hsame row L ∨ hsame row RS ∨ hsame row RG ∨
                          hsame row RM ∨ hsame row RL ∨ hsame row ES ∨ hsame row EG ∨
                            hsame row EM ∨ hsame row EL ∨ hsame row H ∨ hsame row C ∨
                              hsame row P ∨ hsame row N ∨ hsame row additiveRead ∨
                                hsame row multiplicativeRead ∨ hsame row scopedRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont S G additiveRead ∧
                      Cont M L multiplicativeRead ∧
                        Cont additiveRead multiplicativeRead scopedRead ∧
                          PkgSig bundle P pkg ∧ PkgSig bundle scopedRead pkg)
                  hsame ∧ UnaryHistory additiveRead ∧ UnaryHistory multiplicativeRead ∧
                UnaryHistory scopedRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier additiveRoute multiplicativeRoute scopedRoute scopedPkg
  obtain ⟨_aUnary, _bUnary, _waUnary, _wbUnary, _daUnary, _dbUnary, sUnary, gUnary,
    mUnary, lUnary, _rsUnary, _rgUnary, _rmUnary, _rlUnary, _esUnary, _egUnary,
    _emUnary, _elUnary, _hUnary, _cUnary, _pUnary, _nUnary, _sourceWindowA,
    _sourceWindowB, _transportReplay, provenancePkg, _namePkg⟩ := carrier
  have additiveUnary : UnaryHistory additiveRead :=
    unary_cont_closed sUnary gUnary additiveRoute
  have multiplicativeUnary : UnaryHistory multiplicativeRead :=
    unary_cont_closed mUnary lUnary multiplicativeRoute
  have scopedUnary : UnaryHistory scopedRead :=
    unary_cont_closed additiveUnary multiplicativeUnary scopedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row B ∨ hsame row WA ∨ hsame row WB ∨
              hsame row DA ∨ hsame row DB ∨ hsame row S ∨ hsame row G ∨
                hsame row M ∨ hsame row L ∨ hsame row RS ∨ hsame row RG ∨
                  hsame row RM ∨ hsame row RL ∨ hsame row ES ∨ hsame row EG ∨
                    hsame row EM ∨ hsame row EL ∨ hsame row H ∨ hsame row C ∨
                      hsame row P ∨ hsame row N ∨ hsame row additiveRead ∨
                        hsame row multiplicativeRead ∨ hsame row scopedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S G additiveRead ∧ Cont M L multiplicativeRead ∧
              Cont additiveRead multiplicativeRead scopedRead ∧ PkgSig bundle P pkg ∧
                PkgSig bundle scopedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro scopedRead ⟨hsame_refl scopedRead, scopedUnary⟩
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
      repeat right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, additiveRoute, multiplicativeRoute, scopedRoute, provenancePkg,
          scopedPkg⟩
  }
  exact ⟨cert, additiveUnary, multiplicativeUnary, scopedUnary⟩

theorem RegularCauchyRingCarrier_scoped_kernel_dependency [AskSetup] [PackageSetup]
    {A B WA WB DA DB S G M L RS RG RM RL ES EG EM EL H C P N
      sourceSurface operationSurface sealSurface kernelSurface : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyRingCarrier A B WA WB DA DB S G M L RS RG RM RL ES EG EM EL H C P N
        bundle pkg →
      Cont A WA sourceSurface →
        Cont S M operationSurface →
          Cont RS RL sealSurface →
            Cont operationSurface sealSurface kernelSurface →
              PkgSig bundle N pkg →
                SemanticNameCert
                    (fun row : BHist =>
                      hsame row kernelSurface ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row A ∨ hsame row WA ∨ hsame row S ∨ hsame row M ∨
                        hsame row RS ∨ hsame row RL ∨ hsame row sourceSurface ∨
                          hsame row operationSurface ∨ hsame row sealSurface ∨
                            hsame row kernelSurface ∨ hsame row N)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont A WA sourceSurface ∧
                        Cont S M operationSurface ∧ Cont RS RL sealSurface ∧
                          Cont operationSurface sealSurface kernelSurface ∧
                            PkgSig bundle N pkg)
                    hsame ∧
                  UnaryHistory sourceSurface ∧ UnaryHistory operationSurface ∧
                    UnaryHistory sealSurface ∧ UnaryHistory kernelSurface := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg hsame SemanticNameCert UnaryHistory
  intro carrier sourceRoute operationRoute sealRoute kernelRoute namePkg
  obtain ⟨unaryA, _unaryB, unaryWA, _unaryWB, _unaryDA, _unaryDB, unaryS, _unaryG,
    unaryM, _unaryL, unaryRS, _unaryRG, _unaryRM, unaryRL, _unaryES, _unaryEG,
    _unaryEM, _unaryEL, _unaryH, _unaryC, _unaryP, _unaryN, _sourceWindowA,
    _sourceWindowB, _transportReplay, _provenancePkg, _carrierNamePkg⟩ := carrier
  have sourceUnary : UnaryHistory sourceSurface :=
    unary_cont_closed unaryA unaryWA sourceRoute
  have operationUnary : UnaryHistory operationSurface :=
    unary_cont_closed unaryS unaryM operationRoute
  have sealUnary : UnaryHistory sealSurface :=
    unary_cont_closed unaryRS unaryRL sealRoute
  have kernelUnary : UnaryHistory kernelSurface :=
    unary_cont_closed operationUnary sealUnary kernelRoute
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro kernelSurface ⟨hsame_refl kernelSurface, kernelUnary⟩
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
          intro _row _other sameRows sourceRow
          exact
            ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
              unary_transport sourceRow.right sameRows⟩
      }
      pattern_sound := by
        intro _row sourceRow
        exact
          Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inl sourceRow.left)))))))))
      ledger_sound := by
        intro _row sourceRow
        exact
          ⟨sourceRow.right, sourceRoute, operationRoute, sealRoute, kernelRoute, namePkg⟩
    }
  · exact ⟨sourceUnary, operationUnary, sealUnary, kernelUnary⟩

end BEDC.Derived.RegularCauchyRingUp
