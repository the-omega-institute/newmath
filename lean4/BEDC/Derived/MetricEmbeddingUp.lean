import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetricEmbeddingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MetricEmbeddingCarrier (X Y F D R S H C P N : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  UnaryHistory X ∧ UnaryHistory Y ∧ UnaryHistory F ∧ UnaryHistory D ∧
    UnaryHistory R ∧ UnaryHistory S ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory P ∧ UnaryHistory N ∧ Cont X F D ∧ Cont D R S ∧ Cont H C P

theorem MetricEmbeddingCarrier_kernel_scope [AskSetup] [PackageSetup]
    {X Y F D R S H C P N scopeRead : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    MetricEmbeddingCarrier X Y F D R S H C P N →
      Cont S H scopeRead →
        PkgSig bundle P pkg →
          PkgSig bundle N pkg →
            SemanticNameCert
                (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row X ∨ hsame row Y ∨ hsame row F ∨ hsame row D ∨
                    hsame row R ∨ hsame row S ∨ hsame row H ∨ hsame row C ∨
                      hsame row P ∨ hsame row N ∨ hsame row scopeRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont X F D ∧ Cont D R S ∧
                    Cont S H scopeRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                hsame ∧
              UnaryHistory scopeRead := by
  -- BEDC touchpoint anchor: MetricEmbeddingCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier scopeRoute provenancePkg namePkg
  obtain ⟨xUnary, _yUnary, fUnary, _dUnary, rUnary, sUnary, hUnary, _cUnary,
    _pUnary, _nUnary, graphRoute, separatedRoute, _provenanceRoute⟩ := carrier
  have dClosed : UnaryHistory D :=
    unary_cont_closed xUnary fUnary graphRoute
  have sClosed : UnaryHistory S :=
    unary_cont_closed dClosed rUnary separatedRoute
  have scopeUnary : UnaryHistory scopeRead :=
    unary_cont_closed sUnary hUnary scopeRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row Y ∨ hsame row F ∨ hsame row D ∨
              hsame row R ∨ hsame row S ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row N ∨ hsame row scopeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont X F D ∧ Cont D R S ∧ Cont S H scopeRead ∧
              PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro scopeRead ⟨hsame_refl scopeRead, scopeUnary⟩
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
      cases source.left
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
                          (Or.inr (hsame_refl scopeRead))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, graphRoute, separatedRoute, scopeRoute, provenancePkg, namePkg⟩
  }
  exact ⟨cert, scopeUnary⟩

theorem MetricEmbeddingCarrier_public_graph_control_surface [AskSetup] [PackageSetup]
    {X Y F D R S H C P N graphRead controlRead sealedRead separatedRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricEmbeddingCarrier X Y F D R S H C P N ->
      Cont X F graphRead ->
        Cont graphRead D controlRead ->
          Cont controlRead R sealedRead ->
            Cont sealedRead S separatedRead ->
              Cont separatedRead N publicRead ->
                PkgSig bundle P pkg ->
                  PkgSig bundle N pkg ->
                    SemanticNameCert
                        (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row X ∨ hsame row Y ∨ hsame row F ∨ hsame row D ∨
                            hsame row R ∨ hsame row S ∨ hsame row separatedRead ∨
                              hsame row publicRead ∨ hsame row N)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont X F graphRead ∧
                            Cont graphRead D controlRead ∧ Cont controlRead R sealedRead ∧
                              Cont sealedRead S separatedRead ∧
                                Cont separatedRead N publicRead ∧
                                  PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                        hsame ∧
                      UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier graphRoute controlRoute sealedRoute separatedRoute publicRoute provenancePkg namePkg
  obtain ⟨xUnary, _yUnary, fUnary, dUnary, rUnary, sUnary, _hUnary, _cUnary,
    _pUnary, nUnary, _carrierGraphRoute, _carrierSeparatedRoute, _provenanceRoute⟩ :=
    carrier
  have graphUnary : UnaryHistory graphRead :=
    unary_cont_closed xUnary fUnary graphRoute
  have controlUnary : UnaryHistory controlRead :=
    unary_cont_closed graphUnary dUnary controlRoute
  have sealedUnary : UnaryHistory sealedRead :=
    unary_cont_closed controlUnary rUnary sealedRoute
  have separatedUnary : UnaryHistory separatedRead :=
    unary_cont_closed sealedUnary sUnary separatedRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed separatedUnary nUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row Y ∨ hsame row F ∨ hsame row D ∨ hsame row R ∨
              hsame row S ∨ hsame row separatedRead ∨ hsame row publicRead ∨ hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont X F graphRead ∧ Cont graphRead D controlRead ∧
              Cont controlRead R sealedRead ∧ Cont sealedRead S separatedRead ∧
                Cont separatedRead N publicRead ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inl source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, graphRoute, controlRoute, sealedRoute, separatedRoute, publicRoute,
          provenancePkg, namePkg⟩
  }
  exact ⟨cert, publicUnary⟩

theorem MetricEmbeddingCarrier_public_object_surface [AskSetup] [PackageSetup]
    {X Y F D R S H C P N graphRead targetRead controlRead sealRead separatedRead
      objectRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricEmbeddingCarrier X Y F D R S H C P N ->
      Cont X F graphRead ->
        Cont graphRead Y targetRead ->
          Cont targetRead D controlRead ->
            Cont controlRead R sealRead ->
              Cont sealRead S separatedRead ->
                Cont separatedRead N objectRead ->
                  PkgSig bundle P pkg ->
                    PkgSig bundle N pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row objectRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row X ∨ hsame row Y ∨ hsame row F ∨ hsame row D ∨
                              hsame row R ∨ hsame row S ∨ hsame row H ∨ hsame row C ∨
                                hsame row P ∨ hsame row N ∨ hsame row objectRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont X F graphRead ∧
                              Cont graphRead Y targetRead ∧
                                Cont targetRead D controlRead ∧
                                  Cont controlRead R sealRead ∧
                                    Cont sealRead S separatedRead ∧
                                      Cont separatedRead N objectRead ∧
                                        PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                          hsame ∧
                        UnaryHistory objectRead := by
  -- BEDC touchpoint anchor: MetricEmbeddingCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier graphRoute targetRoute controlRoute sealRoute separatedRoute objectRoute
    provenancePkg namePkg
  obtain ⟨xUnary, yUnary, fUnary, dUnary, rUnary, sUnary, _hUnary, _cUnary,
    _pUnary, nUnary, _carrierGraphRoute, _carrierSeparatedRoute, _provenanceRoute⟩ :=
    carrier
  have graphUnary : UnaryHistory graphRead :=
    unary_cont_closed xUnary fUnary graphRoute
  have targetUnary : UnaryHistory targetRead :=
    unary_cont_closed graphUnary yUnary targetRoute
  have controlUnary : UnaryHistory controlRead :=
    unary_cont_closed targetUnary dUnary controlRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed controlUnary rUnary sealRoute
  have separatedUnary : UnaryHistory separatedRead :=
    unary_cont_closed sealUnary sUnary separatedRoute
  have objectUnary : UnaryHistory objectRead :=
    unary_cont_closed separatedUnary nUnary objectRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row objectRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row Y ∨ hsame row F ∨ hsame row D ∨ hsame row R ∨
              hsame row S ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row objectRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont X F graphRead ∧ Cont graphRead Y targetRead ∧
              Cont targetRead D controlRead ∧ Cont controlRead R sealRead ∧
                Cont sealRead S separatedRead ∧ Cont separatedRead N objectRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro objectRead ⟨hsame_refl objectRead, objectUnary⟩
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
                          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, graphRoute, targetRoute, controlRoute, sealRoute, separatedRoute,
          objectRoute, provenancePkg, namePkg⟩
  }
  exact ⟨cert, objectUnary⟩

end BEDC.Derived.MetricEmbeddingUp
