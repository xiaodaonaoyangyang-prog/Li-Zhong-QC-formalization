/-
# 李忠《拟共形映射及其在黎曼曲面论中的应用》 — statement-level Lean 4 formalization

Li Zhong, *Quasiconformal Mappings and Teichmüller Spaces*.

Every definition of the book is given a genuine Lean definition and every theorem, lemma,
corollary and numbered formula is stated with a `sorry` proof.  The files follow the sections of
the book (§1–§36), formalized from the text of the book.
-/
import LiZhongQC.Basic
-- 第一章 拟共形映射的定义与性质
import LiZhongQC.Ch01.S01_Quadrilateral
import LiZhongQC.Ch01.S02_DoublyConnected
import LiZhongQC.Ch01.S03_ExtremalLength
import LiZhongQC.Ch01.S04_ModulusExtremalLength
import LiZhongQC.Ch01.S05_ExtremalProblems
import LiZhongQC.Ch01.S06_C1Quasiconformal
import LiZhongQC.Ch01.S07_GeometricDefinition
import LiZhongQC.Ch01.S08_Compactness
import LiZhongQC.Ch01.S09_AnalyticProperties
import LiZhongQC.Ch01.S10_AnalyticDefinition
-- 第二章 拟共形映射的存在性定理
import LiZhongQC.Ch02.S11_IntegralOperators
import LiZhongQC.Ch02.S11b_HilbertNorm
import LiZhongQC.Ch02.S12_Existence
import LiZhongQC.Ch02.S13_Representation
-- 第三章 偏差定理
import LiZhongQC.Ch03.S14_PoincareMetric
import LiZhongQC.Ch03.S15_Distortion
-- 第四章 拟圆周
import LiZhongQC.Ch04.S16_Quasicircles
import LiZhongQC.Ch04.S17_BoundaryValues
import LiZhongQC.Ch04.S18_BoundedTurning
-- 第五章 拟共形映射与单叶函数
import LiZhongQC.Ch05.S19_Schwarzian
import LiZhongQC.Ch05.S20_SchwarzDomains
import LiZhongQC.Ch05.S21_UniversalTeichmuller
-- 第六章 Riemann 曲面上的拟共形映射
import LiZhongQC.Ch06.S22_RiemannSurfaces
import LiZhongQC.Ch06.S23_QCOnSurfaces
import LiZhongQC.Ch06.S24_QuasiFuchsian
-- 第七章 闭 Riemann 曲面上的极值问题
import LiZhongQC.Ch07.S25_QuadraticDifferentials
import LiZhongQC.Ch07.S26_TeichmullerUniqueness
import LiZhongQC.Ch07.S27_TeichmullerExistence
-- 第八章 Riemann 曲面的模问题与 Teichmüller 空间
import LiZhongQC.Ch08.S28_Moduli
import LiZhongQC.Ch08.S29_TeichmullerMetric
import LiZhongQC.Ch08.S30_ModularGroupDiscontinuity
-- 第九章 有限型 Riemann 曲面上的 Teichmüller 空间
import LiZhongQC.Ch09.S31_FiniteType
import LiZhongQC.Ch09.S32_FiniteTypeTeichmuller
-- 第十章 Bers 有界嵌入定理与 Teichmüller 空间的复结构
import LiZhongQC.Ch10.S33_BersEmbedding
import LiZhongQC.Ch10.S34_BersFiberSpace
-- 第十一章 开 Riemann 曲面上的 Teichmüller 理论
import LiZhongQC.Ch11.S35_DiscTeichmullerMaps
import LiZhongQC.Ch11.S36_Hamilton
-- 辅助引理 Auxiliary lemmas
import LiZhongQC.Lemmas.CrossRatio
import LiZhongQC.Lemmas.GreenRect
import LiZhongQC.Lemmas.GreenDisc
import LiZhongQC.Lemmas.GreenPolar
import LiZhongQC.Lemmas.Pompeiu
import LiZhongQC.Lemmas.DiscAutomorphism
import LiZhongQC.Lemmas.DirichletModulus
import LiZhongQC.RiemannMapping
import LiZhongQC.Lemmas.ConnectedComplement
import LiZhongQC.Lemmas.CanonicalForm
import LiZhongQC.Lemmas.AnnulusQC
import LiZhongQC.Lemmas.InvarianceOfDomain
import LiZhongQC.Lemmas.UnitDiscJordan
import LiZhongQC.Lemmas.EntireLinearGrowth
import LiZhongQC.Lemmas.WeierstrassValues
import LiZhongQC.Lemmas.Koebe
import LiZhongQC.Lemmas.Umlaufsatz
import LiZhongQC.Lemmas.FluxRoute
import LiZhongQC.Lemmas.CZDecomposition
import LiZhongQC.Lemmas.HilbertNormWiring
import LiZhongQC.Lemmas.HilbertInterpPair
import LiZhongQC.Lemmas.HilbertInterp
import LiZhongQC.Lemmas.LpDuality
import LiZhongQC.Lemmas.ExpStripBasic
import LiZhongQC.Lemmas.AnnulusDescent
import LiZhongQC.Lemmas.StripAutomorphism
import LiZhongQC.Lemmas.AnnulusPeriod
import LiZhongQC.Lemmas.ExpStripLift
import LiZhongQC.Lemmas.AnnulusModel
import LiZhongQC.Lemmas.UniformizedTeichmuller
