import InitialLogBounds

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace AgentUCTRealIndex

theorem log_2_interval : ((6931471/10000000):ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ ((433217/625000):ℝ) := by
  apply dyadic_log_interval 2 (0) ((6931471/10000000)) ((433217/625000)) 1 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_3_interval : ((5493061/5000000):ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ ((10986123/10000000):ℝ) := by
  apply dyadic_log_interval 3 ((1/4)) ((5493061/5000000)) ((10986123/10000000)) 2 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_4_interval : ((13862943/10000000):ℝ) ≤ Real.log 4 ∧ Real.log 4 ≤ ((433217/312500):ℝ) := by
  apply dyadic_log_interval 4 (0) ((13862943/10000000)) ((433217/312500)) 2 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_5_interval : ((16094379/10000000):ℝ) ≤ Real.log 5 ∧ Real.log 5 ≤ ((804719/500000):ℝ) := by
  apply dyadic_log_interval 5 ((3/8)) ((16094379/10000000)) ((804719/500000)) 3 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_6_interval : ((8958797/5000000):ℝ) ≤ Real.log 6 ∧ Real.log 6 ≤ ((3583519/2000000):ℝ) := by
  apply dyadic_log_interval 6 ((1/4)) ((8958797/5000000)) ((3583519/2000000)) 3 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_7_interval : ((19459101/10000000):ℝ) ≤ Real.log 7 ∧ Real.log 7 ≤ ((9729551/5000000):ℝ) := by
  apply dyadic_log_interval 7 ((1/8)) ((19459101/10000000)) ((9729551/5000000)) 3 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_8_interval : ((4158883/2000000):ℝ) ≤ Real.log 8 ∧ Real.log 8 ≤ ((1299651/625000):ℝ) := by
  apply dyadic_log_interval 8 (0) ((4158883/2000000)) ((1299651/625000)) 3 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_13_interval : ((25649493/10000000):ℝ) ≤ Real.log 13 ∧ Real.log 13 ≤ ((12824747/5000000):ℝ) := by
  apply dyadic_log_interval 13 ((3/16)) ((25649493/10000000)) ((12824747/5000000)) 4 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_14_interval : ((26390573/10000000):ℝ) ≤ Real.log 14 ∧ Real.log 14 ≤ ((13195287/5000000):ℝ) := by
  apply dyadic_log_interval 14 ((1/8)) ((26390573/10000000)) ((13195287/5000000)) 4 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_15_interval : ((13540251/5000000):ℝ) ≤ Real.log 15 ∧ Real.log 15 ≤ ((27080503/10000000):ℝ) := by
  apply dyadic_log_interval 15 ((1/16)) ((13540251/5000000)) ((27080503/10000000)) 4 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_16_interval : ((27725887/10000000):ℝ) ≤ Real.log 16 ∧ Real.log 16 ≤ ((433217/156250):ℝ) := by
  apply dyadic_log_interval 16 (0) ((27725887/10000000)) ((433217/156250)) 4 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_17_interval : ((28332131/10000000):ℝ) ≤ Real.log 17 ∧ Real.log 17 ≤ ((3541517/1250000):ℝ) := by
  apply dyadic_log_interval 17 ((15/32)) ((28332131/10000000)) ((3541517/1250000)) 5 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_18_interval : ((28903717/10000000):ℝ) ≤ Real.log 18 ∧ Real.log 18 ≤ ((28903719/10000000):ℝ) := by
  apply dyadic_log_interval 18 ((7/16)) ((28903717/10000000)) ((28903719/10000000)) 5 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_19_interval : ((29444389/10000000):ℝ) ≤ Real.log 19 ∧ Real.log 19 ≤ ((2944439/1000000):ℝ) := by
  apply dyadic_log_interval 19 ((13/32)) ((29444389/10000000)) ((2944439/1000000)) 5 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_20_interval : ((14978661/5000000):ℝ) ≤ Real.log 20 ∧ Real.log 20 ≤ ((29957323/10000000):ℝ) := by
  apply dyadic_log_interval 20 ((3/8)) ((14978661/5000000)) ((29957323/10000000)) 5 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_21_interval : ((3805653/1250000):ℝ) ≤ Real.log 21 ∧ Real.log 21 ≤ ((1217809/400000):ℝ) := by
  apply dyadic_log_interval 21 ((11/32)) ((3805653/1250000)) ((1217809/400000)) 5 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_22_interval : ((3863803/1250000):ℝ) ≤ Real.log 22 ∧ Real.log 22 ≤ ((1236417/400000):ℝ) := by
  apply dyadic_log_interval 22 ((5/16)) ((3863803/1250000)) ((1236417/400000)) 5 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_23_interval : ((15677471/5000000):ℝ) ≤ Real.log 23 ∧ Real.log 23 ≤ ((31354943/10000000):ℝ) := by
  apply dyadic_log_interval 23 ((9/32)) ((15677471/5000000)) ((31354943/10000000)) 5 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_24_interval : ((15890269/5000000):ℝ) ≤ Real.log 24 ∧ Real.log 24 ≤ ((31780539/10000000):ℝ) := by
  apply dyadic_log_interval 24 ((1/4)) ((15890269/5000000)) ((31780539/10000000)) 5 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_25_interval : ((16094379/5000000):ℝ) ≤ Real.log 25 ∧ Real.log 25 ≤ ((32188759/10000000):ℝ) := by
  apply dyadic_log_interval 25 ((7/32)) ((16094379/5000000)) ((32188759/10000000)) 5 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_26_interval : ((6516193/2000000):ℝ) ≤ Real.log 26 ∧ Real.log 26 ≤ ((16290483/5000000):ℝ) := by
  apply dyadic_log_interval 26 ((3/16)) ((6516193/2000000)) ((16290483/5000000)) 5 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_27_interval : ((1029949/312500):ℝ) ≤ Real.log 27 ∧ Real.log 27 ≤ ((32958369/10000000):ℝ) := by
  apply dyadic_log_interval 27 ((5/32)) ((1029949/312500)) ((32958369/10000000)) 5 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_28_interval : ((6664409/2000000):ℝ) ≤ Real.log 28 ∧ Real.log 28 ≤ ((16661023/5000000):ℝ) := by
  apply dyadic_log_interval 28 ((1/8)) ((6664409/2000000)) ((16661023/5000000)) 5 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_29_interval : ((16836479/5000000):ℝ) ≤ Real.log 29 ∧ Real.log 29 ≤ ((33672959/10000000):ℝ) := by
  apply dyadic_log_interval 29 ((3/32)) ((16836479/5000000)) ((33672959/10000000)) 5 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_30_interval : ((34011973/10000000):ℝ) ≤ Real.log 30 ∧ Real.log 30 ≤ ((17005987/5000000):ℝ) := by
  apply dyadic_log_interval 30 ((1/16)) ((34011973/10000000)) ((17005987/5000000)) 5 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_31_interval : ((1073121/312500):ℝ) ≤ Real.log 31 ∧ Real.log 31 ≤ ((34339873/10000000):ℝ) := by
  apply dyadic_log_interval 31 ((1/32)) ((1073121/312500)) ((34339873/10000000)) 5 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_32_interval : ((34657359/10000000):ℝ) ≤ Real.log 32 ∧ Real.log 32 ≤ ((433217/125000):ℝ) := by
  apply dyadic_log_interval 32 (0) ((34657359/10000000)) ((433217/125000)) 5 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_33_interval : ((34965071/10000000):ℝ) ≤ Real.log 33 ∧ Real.log 33 ≤ ((34965081/10000000):ℝ) := by
  apply dyadic_log_interval 33 ((31/64)) ((34965071/10000000)) ((34965081/10000000)) 6 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_34_interval : ((35263603/10000000):ℝ) ≤ Real.log 34 ∧ Real.log 34 ≤ ((4407951/1250000):ℝ) := by
  apply dyadic_log_interval 34 ((15/32)) ((35263603/10000000)) ((4407951/1250000)) 6 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_35_interval : ((35553479/10000000):ℝ) ≤ Real.log 35 ∧ Real.log 35 ≤ ((17776741/5000000):ℝ) := by
  apply dyadic_log_interval 35 ((29/64)) ((35553479/10000000)) ((17776741/5000000)) 6 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_36_interval : ((8958797/2500000):ℝ) ≤ Real.log 36 ∧ Real.log 36 ≤ ((3583519/1000000):ℝ) := by
  apply dyadic_log_interval 36 ((7/16)) ((8958797/2500000)) ((3583519/1000000)) 6 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_37_interval : ((18054589/5000000):ℝ) ≤ Real.log 37 ∧ Real.log 37 ≤ ((1805459/500000):ℝ) := by
  apply dyadic_log_interval 37 ((27/64)) ((18054589/5000000)) ((1805459/500000)) 6 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_38_interval : ((36375861/10000000):ℝ) ≤ Real.log 38 ∧ Real.log 38 ≤ ((18187931/5000000):ℝ) := by
  apply dyadic_log_interval 38 ((13/32)) ((36375861/10000000)) ((18187931/5000000)) 6 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_39_interval : ((1144863/312500):ℝ) ≤ Real.log 39 ∧ Real.log 39 ≤ ((36635617/10000000):ℝ) := by
  apply dyadic_log_interval 39 ((25/64)) ((1144863/312500)) ((36635617/10000000)) 6 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_40_interval : ((18444397/5000000):ℝ) ≤ Real.log 40 ∧ Real.log 40 ≤ ((7377759/2000000):ℝ) := by
  apply dyadic_log_interval 40 ((3/8)) ((18444397/5000000)) ((7377759/2000000)) 6 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_41_interval : ((928393/250000):ℝ) ≤ Real.log 41 ∧ Real.log 41 ≤ ((37135721/10000000):ℝ) := by
  apply dyadic_log_interval 41 ((23/64)) ((928393/250000)) ((37135721/10000000)) 6 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_42_interval : ((4672087/1250000):ℝ) ≤ Real.log 42 ∧ Real.log 42 ≤ ((37376697/10000000):ℝ) := by
  apply dyadic_log_interval 42 ((11/32)) ((4672087/1250000)) ((37376697/10000000)) 6 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_43_interval : ((37612001/10000000):ℝ) ≤ Real.log 43 ∧ Real.log 43 ≤ ((18806001/5000000):ℝ) := by
  apply dyadic_log_interval 43 ((21/64)) ((37612001/10000000)) ((18806001/5000000)) 6 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_44_interval : ((4730237/1250000):ℝ) ≤ Real.log 44 ∧ Real.log 44 ≤ ((37841897/10000000):ℝ) := by
  apply dyadic_log_interval 44 ((5/16)) ((4730237/1250000)) ((37841897/10000000)) 6 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_45_interval : ((594791/156250):ℝ) ≤ Real.log 45 ∧ Real.log 45 ≤ ((304533/80000):ℝ) := by
  apply dyadic_log_interval 45 ((19/64)) ((594791/156250)) ((304533/80000)) 6 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

end AgentUCTRealIndex
