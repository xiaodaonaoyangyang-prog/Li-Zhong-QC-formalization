/-
Copyright (c) 2025 LARA, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LARA, EPFL
-/
-- Jordan Curve Theorem: root import file
-- One file per section, following the HOL Light proof structure

-- Phase 1: Discrete Jordan Curve Theorem (Grid Curves)
import JordanCurveTheorem.SectionA_CellGeometry
import JordanCurveTheorem.SectionB_CellTopology
import JordanCurveTheorem.SectionC_Rectagons
import JordanCurveTheorem.SectionD_SegmentInduction
import JordanCurveTheorem.SectionE_Parity
import JordanCurveTheorem.SectionF_IntArith
import JordanCurveTheorem.SectionG_SetTopology
import JordanCurveTheorem.SectionH_Symmetries
-- Graph Theory and Curve Topology
import JordanCurveTheorem.SectionI_GraphTheory
import JordanCurveTheorem.SectionJ_PathConnectivity
import JordanCurveTheorem.SectionK_Analysis
import JordanCurveTheorem.SectionL_ArcTopology
import JordanCurveTheorem.SectionM_ClosedCurveOps
-- K₃,₃ Nonplanarity and Complement Connectivity
import JordanCurveTheorem.SectionN_K33
import JordanCurveTheorem.SectionO_ComplementConnectivity
import JordanCurveTheorem.SectionP_Automation
-- Advanced Parity and Bounded/Unbounded
import JordanCurveTheorem.SectionQ_RectagProps
import JordanCurveTheorem.SectionR_AdvancedParity
import JordanCurveTheorem.SectionS_BoundedUnbounded
-- Grid Approximation
import JordanCurveTheorem.SectionT_GridConstruction
import JordanCurveTheorem.SectionU_Grid33
import JordanCurveTheorem.SectionV_ComplementParity
import JordanCurveTheorem.SectionW_RectagGraphs
import JordanCurveTheorem.SectionX_RationalApprox
import JordanCurveTheorem.SectionY_GridCells
import JordanCurveTheorem.SectionZ_K33Nonplanar
-- Phase 4: Final Assembly
import JordanCurveTheorem.SectionAA_RectagApprox
import JordanCurveTheorem.SectionBB_K33Data
import JordanCurveTheorem.SectionCC_OneSided
import JordanCurveTheorem.SectionDD_JordanCurveTheorem
