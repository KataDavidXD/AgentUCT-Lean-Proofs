import CoreLogBounds

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace AgentUCTRealIndex

theorem log_46_interval : ((38286413/10000000):ℝ) ≤ Real.log 46 ∧ Real.log 46 ≤ ((19143207/5000000):ℝ) := by
  apply dyadic_log_interval 46 ((9/32)) ((38286413/10000000)) ((19143207/5000000)) 6 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_47_interval : ((9625369/2500000):ℝ) ≤ Real.log 47 ∧ Real.log 47 ≤ ((38501477/10000000):ℝ) := by
  apply dyadic_log_interval 47 ((17/64)) ((9625369/2500000)) ((38501477/10000000)) 6 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_48_interval : ((3871201/1000000):ℝ) ≤ Real.log 48 ∧ Real.log 48 ≤ ((38712011/10000000):ℝ) := by
  apply dyadic_log_interval 48 ((1/4)) ((3871201/1000000)) ((38712011/10000000)) 6 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_49_interval : ((19459101/5000000):ℝ) ≤ Real.log 49 ∧ Real.log 49 ≤ ((38918203/10000000):ℝ) := by
  apply dyadic_log_interval 49 ((15/64)) ((19459101/5000000)) ((38918203/10000000)) 6 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_50_interval : ((3912023/1000000):ℝ) ≤ Real.log 50 ∧ Real.log 50 ≤ ((39120231/10000000):ℝ) := by
  apply dyadic_log_interval 50 ((7/32)) ((3912023/1000000)) ((39120231/10000000)) 6 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_51_interval : ((2457391/625000):ℝ) ≤ Real.log 51 ∧ Real.log 51 ≤ ((39318257/10000000):ℝ) := by
  apply dyadic_log_interval 51 ((13/64)) ((2457391/625000)) ((39318257/10000000)) 6 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_52_interval : ((39512437/10000000):ℝ) ≤ Real.log 52 ∧ Real.log 52 ≤ ((19756219/5000000):ℝ) := by
  apply dyadic_log_interval 52 ((3/16)) ((39512437/10000000)) ((19756219/5000000)) 6 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_53_interval : ((39702919/10000000):ℝ) ≤ Real.log 53 ∧ Real.log 53 ≤ ((992573/250000):ℝ) := by
  apply dyadic_log_interval 53 ((11/64)) ((39702919/10000000)) ((992573/250000)) 6 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_54_interval : ((498623/125000):ℝ) ≤ Real.log 54 ∧ Real.log 54 ≤ ((39889841/10000000):ℝ) := by
  apply dyadic_log_interval 54 ((5/32)) ((498623/125000)) ((39889841/10000000)) 6 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_55_interval : ((40073331/10000000):ℝ) ≤ Real.log 55 ∧ Real.log 55 ≤ ((10018333/2500000):ℝ) := by
  apply dyadic_log_interval 55 ((9/64)) ((40073331/10000000)) ((10018333/2500000)) 6 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_56_interval : ((10063379/2500000):ℝ) ≤ Real.log 56 ∧ Real.log 56 ≤ ((40253517/10000000):ℝ) := by
  apply dyadic_log_interval 56 ((1/8)) ((10063379/2500000)) ((40253517/10000000)) 6 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_57_interval : ((2526907/625000):ℝ) ≤ Real.log 57 ∧ Real.log 57 ≤ ((40430513/10000000):ℝ) := by
  apply dyadic_log_interval 57 ((7/64)) ((2526907/625000)) ((40430513/10000000)) 6 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_58_interval : ((4060443/1000000):ℝ) ≤ Real.log 58 ∧ Real.log 58 ≤ ((40604431/10000000):ℝ) := by
  apply dyadic_log_interval 58 ((3/32)) ((4060443/1000000)) ((40604431/10000000)) 6 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_59_interval : ((20387687/5000000):ℝ) ≤ Real.log 59 ∧ Real.log 59 ≤ ((326203/80000):ℝ) := by
  apply dyadic_log_interval 59 ((5/64)) ((20387687/5000000)) ((326203/80000)) 6 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_60_interval : ((8188689/2000000):ℝ) ≤ Real.log 60 ∧ Real.log 60 ≤ ((20471723/5000000):ℝ) := by
  apply dyadic_log_interval 60 ((1/16)) ((8188689/2000000)) ((20471723/5000000)) 6 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_61_interval : ((20554369/5000000):ℝ) ≤ Real.log 61 ∧ Real.log 61 ≤ ((41108739/10000000):ℝ) := by
  apply dyadic_log_interval 61 ((3/64)) ((20554369/5000000)) ((41108739/10000000)) 6 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_62_interval : ((41271343/10000000):ℝ) ≤ Real.log 62 ∧ Real.log 62 ≤ ((2579459/625000):ℝ) := by
  apply dyadic_log_interval 62 ((1/32)) ((41271343/10000000)) ((2579459/625000)) 6 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_63_interval : ((41431347/10000000):ℝ) ≤ Real.log 63 ∧ Real.log 63 ≤ ((10357837/2500000):ℝ) := by
  apply dyadic_log_interval 63 ((1/64)) ((41431347/10000000)) ((10357837/2500000)) 6 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_64_interval : ((4158883/1000000):ℝ) ≤ Real.log 64 ∧ Real.log 64 ≤ ((41588831/10000000):ℝ) := by
  apply dyadic_log_interval 64 (0) ((4158883/1000000)) ((41588831/10000000)) 6 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_65_interval : ((20871933/5000000):ℝ) ≤ Real.log 65 ∧ Real.log 65 ≤ ((1043597/250000):ℝ) := by
  apply dyadic_log_interval 65 ((63/128)) ((20871933/5000000)) ((1043597/250000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_66_interval : ((20948271/5000000):ℝ) ≤ Real.log 66 ∧ Real.log 66 ≤ ((41896553/10000000):ℝ) := by
  apply dyadic_log_interval 66 ((31/64)) ((20948271/5000000)) ((41896553/10000000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_67_interval : ((42046923/10000000):ℝ) ≤ Real.log 67 ∧ Real.log 67 ≤ ((4204693/1000000):ℝ) := by
  apply dyadic_log_interval 67 ((61/128)) ((42046923/10000000)) ((4204693/1000000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_68_interval : ((21097537/5000000):ℝ) ≤ Real.log 68 ∧ Real.log 68 ≤ ((1054877/250000):ℝ) := by
  apply dyadic_log_interval 68 ((15/32)) ((21097537/5000000)) ((1054877/250000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_69_interval : ((42341063/10000000):ℝ) ≤ Real.log 69 ∧ Real.log 69 ≤ ((42341067/10000000):ℝ) := by
  apply dyadic_log_interval 69 ((59/128)) ((42341063/10000000)) ((42341067/10000000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_70_interval : ((42484951/10000000):ℝ) ≤ Real.log 70 ∧ Real.log 70 ≤ ((21242477/5000000):ℝ) := by
  apply dyadic_log_interval 70 ((29/64)) ((42484951/10000000)) ((21242477/5000000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_71_interval : ((21313399/5000000):ℝ) ≤ Real.log 71 ∧ Real.log 71 ≤ ((106567/25000):ℝ) := by
  apply dyadic_log_interval 71 ((57/128)) ((21313399/5000000)) ((106567/25000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_72_interval : ((2138333/500000):ℝ) ≤ Real.log 72 ∧ Real.log 72 ≤ ((21383331/5000000):ℝ) := by
  apply dyadic_log_interval 72 ((7/16)) ((2138333/500000)) ((21383331/5000000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_73_interval : ((21452297/5000000):ℝ) ≤ Real.log 73 ∧ Real.log 73 ≤ ((8580919/2000000):ℝ) := by
  apply dyadic_log_interval 73 ((55/128)) ((21452297/5000000)) ((8580919/2000000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_74_interval : ((860813/200000):ℝ) ≤ Real.log 74 ∧ Real.log 74 ≤ ((10760163/2500000):ℝ) := by
  apply dyadic_log_interval 74 ((27/64)) ((860813/200000)) ((10760163/2500000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_75_interval : ((269843/62500):ℝ) ≤ Real.log 75 ∧ Real.log 75 ≤ ((21587441/5000000):ℝ) := by
  apply dyadic_log_interval 75 ((53/128)) ((269843/62500)) ((21587441/5000000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_76_interval : ((43307333/10000000):ℝ) ≤ Real.log 76 ∧ Real.log 76 ≤ ((21653667/5000000):ℝ) := by
  apply dyadic_log_interval 76 ((13/32)) ((43307333/10000000)) ((21653667/5000000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_77_interval : ((21719027/5000000):ℝ) ≤ Real.log 77 ∧ Real.log 77 ≤ ((8687611/2000000):ℝ) := by
  apply dyadic_log_interval 77 ((51/128)) ((21719027/5000000)) ((8687611/2000000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_78_interval : ((2722943/625000):ℝ) ≤ Real.log 78 ∧ Real.log 78 ≤ ((43567089/10000000):ℝ) := by
  apply dyadic_log_interval 78 ((25/64)) ((2722943/625000)) ((43567089/10000000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_79_interval : ((21847239/5000000):ℝ) ≤ Real.log 79 ∧ Real.log 79 ≤ ((43694479/10000000):ℝ) := by
  apply dyadic_log_interval 79 ((49/128)) ((21847239/5000000)) ((43694479/10000000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_80_interval : ((21910133/5000000):ℝ) ≤ Real.log 80 ∧ Real.log 80 ≤ ((43820267/10000000):ℝ) := by
  apply dyadic_log_interval 80 ((3/8)) ((21910133/5000000)) ((43820267/10000000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_81_interval : ((43944491/10000000):ℝ) ≤ Real.log 81 ∧ Real.log 81 ≤ ((10986123/2500000):ℝ) := by
  apply dyadic_log_interval 81 ((47/128)) ((43944491/10000000)) ((10986123/2500000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_82_interval : ((5508399/1250000):ℝ) ≤ Real.log 82 ∧ Real.log 82 ≤ ((44067193/10000000):ℝ) := by
  apply dyadic_log_interval 82 ((23/64)) ((5508399/1250000)) ((44067193/10000000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_83_interval : ((22094203/5000000):ℝ) ≤ Real.log 83 ∧ Real.log 83 ≤ ((44188407/10000000):ℝ) := by
  apply dyadic_log_interval 83 ((45/128)) ((22094203/5000000)) ((44188407/10000000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_84_interval : ((44308167/10000000):ℝ) ≤ Real.log 84 ∧ Real.log 84 ≤ ((44308169/10000000):ℝ) := by
  apply dyadic_log_interval 84 ((11/32)) ((44308167/10000000)) ((44308169/10000000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_85_interval : ((2776657/625000):ℝ) ≤ Real.log 85 ∧ Real.log 85 ≤ ((44426513/10000000):ℝ) := by
  apply dyadic_log_interval 85 ((43/128)) ((2776657/625000)) ((44426513/10000000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_86_interval : ((2783967/625000):ℝ) ≤ Real.log 86 ∧ Real.log 86 ≤ ((44543473/10000000):ℝ) := by
  apply dyadic_log_interval 86 ((21/64)) ((2783967/625000)) ((44543473/10000000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_87_interval : ((44659081/10000000):ℝ) ≤ Real.log 87 ∧ Real.log 87 ≤ ((22329541/5000000):ℝ) := by
  apply dyadic_log_interval 87 ((41/128)) ((44659081/10000000)) ((22329541/5000000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_88_interval : ((5596671/1250000):ℝ) ≤ Real.log 88 ∧ Real.log 88 ≤ ((44773369/10000000):ℝ) := by
  apply dyadic_log_interval 88 ((5/16)) ((5596671/1250000)) ((44773369/10000000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_89_interval : ((44886363/10000000):ℝ) ≤ Real.log 89 ∧ Real.log 89 ≤ ((11221591/2500000):ℝ) := by
  apply dyadic_log_interval 89 ((39/128)) ((44886363/10000000)) ((11221591/2500000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_90_interval : ((2812381/625000):ℝ) ≤ Real.log 90 ∧ Real.log 90 ≤ ((44998097/10000000):ℝ) := by
  apply dyadic_log_interval 90 ((19/64)) ((2812381/625000)) ((44998097/10000000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_91_interval : ((9021719/2000000):ℝ) ≤ Real.log 91 ∧ Real.log 91 ≤ ((11277149/2500000):ℝ) := by
  apply dyadic_log_interval 91 ((37/128)) ((9021719/2000000)) ((11277149/2500000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_92_interval : ((9043577/2000000):ℝ) ≤ Real.log 92 ∧ Real.log 92 ≤ ((22608943/5000000):ℝ) := by
  apply dyadic_log_interval 92 ((9/32)) ((9043577/2000000)) ((22608943/5000000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_93_interval : ((22662997/5000000):ℝ) ≤ Real.log 93 ∧ Real.log 93 ≤ ((9065199/2000000):ℝ) := by
  apply dyadic_log_interval 93 ((35/128)) ((22662997/5000000)) ((9065199/2000000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_94_interval : ((45432947/10000000):ℝ) ≤ Real.log 94 ∧ Real.log 94 ≤ ((11358237/2500000):ℝ) := by
  apply dyadic_log_interval 94 ((17/64)) ((45432947/10000000)) ((11358237/2500000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_95_interval : ((2846173/625000):ℝ) ≤ Real.log 95 ∧ Real.log 95 ≤ ((45538769/10000000):ℝ) := by
  apply dyadic_log_interval 95 ((33/128)) ((2846173/625000)) ((45538769/10000000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_96_interval : ((45643481/10000000):ℝ) ≤ Real.log 96 ∧ Real.log 96 ≤ ((22821741/5000000):ℝ) := by
  apply dyadic_log_interval 96 ((1/4)) ((45643481/10000000)) ((22821741/5000000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_97_interval : ((45747109/10000000):ℝ) ≤ Real.log 97 ∧ Real.log 97 ≤ ((4574711/1000000):ℝ) := by
  apply dyadic_log_interval 97 ((31/128)) ((45747109/10000000)) ((4574711/1000000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_98_interval : ((22924837/5000000):ℝ) ≤ Real.log 98 ∧ Real.log 98 ≤ ((1833987/400000):ℝ) := by
  apply dyadic_log_interval 98 ((15/64)) ((22924837/5000000)) ((1833987/400000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_99_interval : ((22975599/5000000):ℝ) ≤ Real.log 99 ∧ Real.log 99 ≤ ((45951199/10000000):ℝ) := by
  apply dyadic_log_interval 99 ((29/128)) ((22975599/5000000)) ((45951199/10000000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_100_interval : ((46051701/10000000):ℝ) ≤ Real.log 100 ∧ Real.log 100 ≤ ((23025851/5000000):ℝ) := by
  apply dyadic_log_interval 100 ((7/32)) ((46051701/10000000)) ((23025851/5000000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_101_interval : ((9230241/2000000):ℝ) ≤ Real.log 101 ∧ Real.log 101 ≤ ((23075603/5000000):ℝ) := by
  apply dyadic_log_interval 101 ((27/128)) ((9230241/2000000)) ((23075603/5000000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_102_interval : ((361326/78125):ℝ) ≤ Real.log 102 ∧ Real.log 102 ≤ ((46249729/10000000):ℝ) := by
  apply dyadic_log_interval 102 ((13/64)) ((361326/78125)) ((46249729/10000000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_103_interval : ((46347289/10000000):ℝ) ≤ Real.log 103 ∧ Real.log 103 ≤ ((4634729/1000000):ℝ) := by
  apply dyadic_log_interval 103 ((25/128)) ((46347289/10000000)) ((4634729/1000000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_104_interval : ((11610977/2500000):ℝ) ≤ Real.log 104 ∧ Real.log 104 ≤ ((4644391/1000000):ℝ) := by
  apply dyadic_log_interval 104 ((3/16)) ((11610977/2500000)) ((4644391/1000000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_105_interval : ((46539603/10000000):ℝ) ≤ Real.log 105 ∧ Real.log 105 ≤ ((11634901/2500000):ℝ) := by
  apply dyadic_log_interval 105 ((23/128)) ((46539603/10000000)) ((11634901/2500000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_106_interval : ((4663439/1000000):ℝ) ≤ Real.log 106 ∧ Real.log 106 ≤ ((46634391/10000000):ℝ) := by
  apply dyadic_log_interval 106 ((11/64)) ((4663439/1000000)) ((46634391/10000000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_107_interval : ((1460259/312500):ℝ) ≤ Real.log 107 ∧ Real.log 107 ≤ ((46728289/10000000):ℝ) := by
  apply dyadic_log_interval 107 ((21/128)) ((1460259/312500)) ((46728289/10000000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_108_interval : ((731583/156250):ℝ) ≤ Real.log 108 ∧ Real.log 108 ≤ ((46821313/10000000):ℝ) := by
  apply dyadic_log_interval 108 ((5/32)) ((731583/156250)) ((46821313/10000000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_109_interval : ((23456739/5000000):ℝ) ≤ Real.log 109 ∧ Real.log 109 ≤ ((46913479/10000000):ℝ) := by
  apply dyadic_log_interval 109 ((19/128)) ((23456739/5000000)) ((46913479/10000000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_110_interval : ((47004803/10000000):ℝ) ≤ Real.log 110 ∧ Real.log 110 ≤ ((11751201/2500000):ℝ) := by
  apply dyadic_log_interval 110 ((9/64)) ((47004803/10000000)) ((11751201/2500000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_111_interval : ((47095301/10000000):ℝ) ≤ Real.log 111 ∧ Real.log 111 ≤ ((47095303/10000000):ℝ) := by
  apply dyadic_log_interval 111 ((17/128)) ((47095301/10000000)) ((47095303/10000000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_112_interval : ((11796247/2500000):ℝ) ≤ Real.log 112 ∧ Real.log 112 ≤ ((47184989/10000000):ℝ) := by
  apply dyadic_log_interval 112 ((1/8)) ((11796247/2500000)) ((47184989/10000000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_113_interval : ((23636939/5000000):ℝ) ≤ Real.log 113 ∧ Real.log 113 ≤ ((47273879/10000000):ℝ) := by
  apply dyadic_log_interval 113 ((15/128)) ((23636939/5000000)) ((47273879/10000000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_114_interval : ((740031/156250):ℝ) ≤ Real.log 114 ∧ Real.log 114 ≤ ((9472397/2000000):ℝ) := by
  apply dyadic_log_interval 114 ((7/64)) ((740031/156250)) ((9472397/2000000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_115_interval : ((47449321/10000000):ℝ) ≤ Real.log 115 ∧ Real.log 115 ≤ ((23724661/5000000):ℝ) := by
  apply dyadic_log_interval 115 ((13/128)) ((47449321/10000000)) ((23724661/5000000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_116_interval : ((47535901/10000000):ℝ) ≤ Real.log 116 ∧ Real.log 116 ≤ ((23767951/5000000):ℝ) := by
  apply dyadic_log_interval 116 ((3/32)) ((47535901/10000000)) ((23767951/5000000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_117_interval : ((47621739/10000000):ℝ) ≤ Real.log 117 ∧ Real.log 117 ≤ ((2381087/500000):ℝ) := by
  apply dyadic_log_interval 117 ((11/128)) ((47621739/10000000)) ((2381087/500000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_118_interval : ((23853423/5000000):ℝ) ≤ Real.log 118 ∧ Real.log 118 ≤ ((47706847/10000000):ℝ) := by
  apply dyadic_log_interval 118 ((5/64)) ((23853423/5000000)) ((47706847/10000000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_119_interval : ((23895617/5000000):ℝ) ≤ Real.log 119 ∧ Real.log 119 ≤ ((9558247/2000000):ℝ) := by
  apply dyadic_log_interval 119 ((9/128)) ((23895617/5000000)) ((9558247/2000000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_120_interval : ((47874917/10000000):ℝ) ≤ Real.log 120 ∧ Real.log 120 ≤ ((23937459/5000000):ℝ) := by
  apply dyadic_log_interval 120 ((1/16)) ((47874917/10000000)) ((23937459/5000000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_121_interval : ((9591581/2000000):ℝ) ≤ Real.log 121 ∧ Real.log 121 ≤ ((23978953/5000000):ℝ) := by
  apply dyadic_log_interval 121 ((7/128)) ((9591581/2000000)) ((23978953/5000000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_122_interval : ((4804021/1000000):ℝ) ≤ Real.log 122 ∧ Real.log 122 ≤ ((48040211/10000000):ℝ) := by
  apply dyadic_log_interval 122 ((3/64)) ((4804021/1000000)) ((48040211/10000000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_123_interval : ((48121843/10000000):ℝ) ≤ Real.log 123 ∧ Real.log 123 ≤ ((12030461/2500000):ℝ) := by
  apply dyadic_log_interval 123 ((5/128)) ((48121843/10000000)) ((12030461/2500000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_124_interval : ((9640563/2000000):ℝ) ≤ Real.log 124 ∧ Real.log 124 ≤ ((753169/156250):ℝ) := by
  apply dyadic_log_interval 124 ((1/32)) ((9640563/2000000)) ((753169/156250)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_125_interval : ((48283137/10000000):ℝ) ≤ Real.log 125 ∧ Real.log 125 ≤ ((24141569/5000000):ℝ) := by
  apply dyadic_log_interval 125 ((3/128)) ((48283137/10000000)) ((24141569/5000000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_126_interval : ((48362819/10000000):ℝ) ≤ Real.log 126 ∧ Real.log 126 ≤ ((2418141/500000):ℝ) := by
  apply dyadic_log_interval 126 ((1/64)) ((48362819/10000000)) ((2418141/500000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_127_interval : ((4844187/1000000):ℝ) ≤ Real.log 127 ∧ Real.log 127 ≤ ((48441871/10000000):ℝ) := by
  apply dyadic_log_interval 127 ((1/128)) ((4844187/1000000)) ((48441871/10000000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_128_interval : ((24260151/5000000):ℝ) ≤ Real.log 128 ∧ Real.log 128 ≤ ((48520303/10000000):ℝ) := by
  apply dyadic_log_interval 128 (0) ((24260151/5000000)) ((48520303/10000000)) 7 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_129_interval : ((12149529/2500000):ℝ) ≤ Real.log 129 ∧ Real.log 129 ≤ ((48598133/10000000):ℝ) := by
  apply dyadic_log_interval 129 ((127/256)) ((12149529/2500000)) ((48598133/10000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_130_interval : ((24337669/5000000):ℝ) ≤ Real.log 130 ∧ Real.log 130 ≤ ((6084419/1250000):ℝ) := by
  apply dyadic_log_interval 130 ((63/128)) ((24337669/5000000)) ((6084419/1250000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_131_interval : ((48751967/10000000):ℝ) ≤ Real.log 131 ∧ Real.log 131 ≤ ((2437599/500000):ℝ) := by
  apply dyadic_log_interval 131 ((125/256)) ((48751967/10000000)) ((2437599/500000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_132_interval : ((24414007/5000000):ℝ) ≤ Real.log 132 ∧ Real.log 132 ≤ ((1953121/400000):ℝ) := by
  apply dyadic_log_interval 132 ((31/64)) ((24414007/5000000)) ((1953121/400000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_133_interval : ((48903487/10000000):ℝ) ≤ Real.log 133 ∧ Real.log 133 ≤ ((6112937/1250000):ℝ) := by
  apply dyadic_log_interval 133 ((123/256)) ((48903487/10000000)) ((6112937/1250000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_134_interval : ((24489197/5000000):ℝ) ≤ Real.log 134 ∧ Real.log 134 ≤ ((24489201/5000000):ℝ) := by
  apply dyadic_log_interval 134 ((61/128)) ((24489197/5000000)) ((24489201/5000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_135_interval : ((9810549/2000000):ℝ) ≤ Real.log 135 ∧ Real.log 135 ≤ ((49052751/10000000):ℝ) := by
  apply dyadic_log_interval 135 ((121/256)) ((9810549/2000000)) ((49052751/10000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_136_interval : ((24563273/5000000):ℝ) ≤ Real.log 136 ∧ Real.log 136 ≤ ((6140819/1250000):ℝ) := by
  apply dyadic_log_interval 136 ((15/32)) ((24563273/5000000)) ((6140819/1250000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_137_interval : ((49199807/10000000):ℝ) ≤ Real.log 137 ∧ Real.log 137 ≤ ((12299953/2500000):ℝ) := by
  apply dyadic_log_interval 137 ((119/256)) ((49199807/10000000)) ((12299953/2500000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_138_interval : ((9854507/2000000):ℝ) ≤ Real.log 138 ∧ Real.log 138 ≤ ((49272539/10000000):ℝ) := by
  apply dyadic_log_interval 138 ((59/128)) ((9854507/2000000)) ((49272539/10000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_139_interval : ((24672369/5000000):ℝ) ≤ Real.log 139 ∧ Real.log 139 ≤ ((49344741/10000000):ℝ) := by
  apply dyadic_log_interval 139 ((117/256)) ((24672369/5000000)) ((49344741/10000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_140_interval : ((49416423/10000000):ℝ) ≤ Real.log 140 ∧ Real.log 140 ≤ ((24708213/5000000):ℝ) := by
  apply dyadic_log_interval 140 ((29/64)) ((49416423/10000000)) ((24708213/5000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_141_interval : ((24743799/5000000):ℝ) ≤ Real.log 141 ∧ Real.log 141 ≤ ((123719/25000):ℝ) := by
  apply dyadic_log_interval 141 ((115/256)) ((24743799/5000000)) ((123719/25000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_142_interval : ((49558269/10000000):ℝ) ≤ Real.log 142 ∧ Real.log 142 ≤ ((387174/78125):ℝ) := by
  apply dyadic_log_interval 142 ((57/128)) ((49558269/10000000)) ((387174/78125)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_143_interval : ((9925689/2000000):ℝ) ≤ Real.log 143 ∧ Real.log 143 ≤ ((49628447/10000000):ℝ) := by
  apply dyadic_log_interval 143 ((113/256)) ((9925689/2000000)) ((49628447/10000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_144_interval : ((12424533/2500000):ℝ) ≤ Real.log 144 ∧ Real.log 144 ≤ ((24849067/5000000):ℝ) := by
  apply dyadic_log_interval 144 ((7/16)) ((12424533/2500000)) ((24849067/5000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_145_interval : ((49767337/10000000):ℝ) ≤ Real.log 145 ∧ Real.log 145 ≤ ((24883669/5000000):ℝ) := by
  apply dyadic_log_interval 145 ((111/256)) ((49767337/10000000)) ((24883669/5000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_146_interval : ((9967213/2000000):ℝ) ≤ Real.log 146 ∧ Real.log 146 ≤ ((49836067/10000000):ℝ) := by
  apply dyadic_log_interval 146 ((55/128)) ((9967213/2000000)) ((49836067/10000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_147_interval : ((1996173/400000):ℝ) ≤ Real.log 147 ∧ Real.log 147 ≤ ((49904327/10000000):ℝ) := by
  apply dyadic_log_interval 147 ((109/256)) ((1996173/400000)) ((49904327/10000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_148_interval : ((24986061/5000000):ℝ) ≤ Real.log 148 ∧ Real.log 148 ≤ ((12493031/2500000):ℝ) := by
  apply dyadic_log_interval 148 ((27/64)) ((24986061/5000000)) ((12493031/2500000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_149_interval : ((25019731/5000000):ℝ) ≤ Real.log 149 ∧ Real.log 149 ≤ ((6254933/1250000):ℝ) := by
  apply dyadic_log_interval 149 ((107/256)) ((25019731/5000000)) ((6254933/1250000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_150_interval : ((3131647/625000):ℝ) ≤ Real.log 150 ∧ Real.log 150 ≤ ((25053177/5000000):ℝ) := by
  apply dyadic_log_interval 150 ((53/128)) ((3131647/625000)) ((25053177/5000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_151_interval : ((25086399/5000000):ℝ) ≤ Real.log 151 ∧ Real.log 151 ≤ ((50172799/10000000):ℝ) := by
  apply dyadic_log_interval 151 ((105/256)) ((25086399/5000000)) ((50172799/10000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_152_interval : ((10047761/2000000):ℝ) ≤ Real.log 152 ∧ Real.log 152 ≤ ((25119403/5000000):ℝ) := by
  apply dyadic_log_interval 152 ((13/32)) ((10047761/2000000)) ((25119403/5000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_153_interval : ((50304379/10000000):ℝ) ≤ Real.log 153 ∧ Real.log 153 ≤ ((2515219/500000):ℝ) := by
  apply dyadic_log_interval 153 ((103/256)) ((50304379/10000000)) ((2515219/500000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_154_interval : ((2014781/400000):ℝ) ≤ Real.log 154 ∧ Real.log 154 ≤ ((50369527/10000000):ℝ) := by
  apply dyadic_log_interval 154 ((51/128)) ((2014781/400000)) ((50369527/10000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_155_interval : ((50434251/10000000):ℝ) ≤ Real.log 155 ∧ Real.log 155 ≤ ((12608563/2500000):ℝ) := by
  apply dyadic_log_interval 155 ((101/256)) ((50434251/10000000)) ((12608563/2500000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_156_interval : ((78904/15625):ℝ) ≤ Real.log 156 ∧ Real.log 156 ≤ ((50498561/10000000):ℝ) := by
  apply dyadic_log_interval 156 ((25/64)) ((78904/15625)) ((50498561/10000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_157_interval : ((50562457/10000000):ℝ) ≤ Real.log 157 ∧ Real.log 157 ≤ ((50562459/10000000):ℝ) := by
  apply dyadic_log_interval 157 ((99/256)) ((50562457/10000000)) ((50562459/10000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_158_interval : ((1012519/200000):ℝ) ≤ Real.log 158 ∧ Real.log 158 ≤ ((50625951/10000000):ℝ) := by
  apply dyadic_log_interval 158 ((49/128)) ((1012519/200000)) ((50625951/10000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_159_interval : ((50689041/10000000):ℝ) ≤ Real.log 159 ∧ Real.log 159 ≤ ((50689043/10000000):ℝ) := by
  apply dyadic_log_interval 159 ((97/256)) ((50689041/10000000)) ((50689043/10000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_160_interval : ((25375869/5000000):ℝ) ≤ Real.log 160 ∧ Real.log 160 ≤ ((50751739/10000000):ℝ) := by
  apply dyadic_log_interval 160 ((3/8)) ((25375869/5000000)) ((50751739/10000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_161_interval : ((50814043/10000000):ℝ) ≤ Real.log 161 ∧ Real.log 161 ≤ ((12703511/2500000):ℝ) := by
  apply dyadic_log_interval 161 ((95/256)) ((50814043/10000000)) ((12703511/2500000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_162_interval : ((50875963/10000000):ℝ) ≤ Real.log 162 ∧ Real.log 162 ≤ ((12718991/2500000):ℝ) := by
  apply dyadic_log_interval 162 ((47/128)) ((50875963/10000000)) ((12718991/2500000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_163_interval : ((50937501/10000000):ℝ) ≤ Real.log 163 ∧ Real.log 163 ≤ ((50937503/10000000):ℝ) := by
  apply dyadic_log_interval 163 ((93/256)) ((50937501/10000000)) ((50937503/10000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_164_interval : ((6374833/1250000):ℝ) ≤ Real.log 164 ∧ Real.log 164 ≤ ((10199733/2000000):ℝ) := by
  apply dyadic_log_interval 164 ((23/64)) ((6374833/1250000)) ((10199733/2000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_165_interval : ((25529727/5000000):ℝ) ≤ Real.log 165 ∧ Real.log 165 ≤ ((10211891/2000000):ℝ) := by
  apply dyadic_log_interval 165 ((91/256)) ((25529727/5000000)) ((10211891/2000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_166_interval : ((51119877/10000000):ℝ) ≤ Real.log 166 ∧ Real.log 166 ≤ ((25559939/5000000):ℝ) := by
  apply dyadic_log_interval 166 ((45/128)) ((51119877/10000000)) ((25559939/5000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_167_interval : ((25589969/5000000):ℝ) ≤ Real.log 167 ∧ Real.log 167 ≤ ((51179939/10000000):ℝ) := by
  apply dyadic_log_interval 167 ((89/256)) ((25589969/5000000)) ((51179939/10000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_168_interval : ((51239639/10000000):ℝ) ≤ Real.log 168 ∧ Real.log 168 ≤ ((1280991/250000):ℝ) := by
  apply dyadic_log_interval 168 ((11/32)) ((51239639/10000000)) ((1280991/250000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_169_interval : ((51298987/10000000):ℝ) ≤ Real.log 169 ∧ Real.log 169 ≤ ((12824747/2500000):ℝ) := by
  apply dyadic_log_interval 169 ((87/256)) ((51298987/10000000)) ((12824747/2500000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_170_interval : ((1604937/312500):ℝ) ≤ Real.log 170 ∧ Real.log 170 ≤ ((10271597/2000000):ℝ) := by
  apply dyadic_log_interval 170 ((43/128)) ((1604937/312500)) ((10271597/2000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_171_interval : ((10283327/2000000):ℝ) ≤ Real.log 171 ∧ Real.log 171 ≤ ((12854159/2500000):ℝ) := by
  apply dyadic_log_interval 171 ((85/256)) ((10283327/2000000)) ((12854159/2500000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_172_interval : ((402148/78125):ℝ) ≤ Real.log 172 ∧ Real.log 172 ≤ ((10294989/2000000):ℝ) := by
  apply dyadic_log_interval 172 ((21/64)) ((402148/78125)) ((10294989/2000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_173_interval : ((10306583/2000000):ℝ) ≤ Real.log 173 ∧ Real.log 173 ≤ ((12883229/2500000):ℝ) := by
  apply dyadic_log_interval 173 ((83/256)) ((10306583/2000000)) ((12883229/2500000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_174_interval : ((6448819/1250000):ℝ) ≤ Real.log 174 ∧ Real.log 174 ≤ ((25795277/5000000):ℝ) := by
  apply dyadic_log_interval 174 ((41/128)) ((6448819/1250000)) ((25795277/5000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_175_interval : ((51647859/10000000):ℝ) ≤ Real.log 175 ∧ Real.log 175 ≤ ((2582393/500000):ℝ) := by
  apply dyadic_log_interval 175 ((81/256)) ((51647859/10000000)) ((2582393/500000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_176_interval : ((51704839/10000000):ℝ) ≤ Real.log 176 ∧ Real.log 176 ≤ ((1292621/250000):ℝ) := by
  apply dyadic_log_interval 176 ((5/16)) ((51704839/10000000)) ((1292621/250000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_177_interval : ((51761497/10000000):ℝ) ≤ Real.log 177 ∧ Real.log 177 ≤ ((25880749/5000000):ℝ) := by
  apply dyadic_log_interval 177 ((79/256)) ((51761497/10000000)) ((25880749/5000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_178_interval : ((10363567/2000000):ℝ) ≤ Real.log 178 ∧ Real.log 178 ≤ ((12954459/2500000):ℝ) := by
  apply dyadic_log_interval 178 ((39/128)) ((10363567/2000000)) ((12954459/2500000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_179_interval : ((25936929/5000000):ℝ) ≤ Real.log 179 ∧ Real.log 179 ≤ ((51873859/10000000):ℝ) := by
  apply dyadic_log_interval 179 ((77/256)) ((25936929/5000000)) ((51873859/10000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_180_interval : ((1622799/312500):ℝ) ≤ Real.log 180 ∧ Real.log 180 ≤ ((51929569/10000000):ℝ) := by
  apply dyadic_log_interval 180 ((19/64)) ((1622799/312500)) ((51929569/10000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_181_interval : ((5198497/1000000):ℝ) ≤ Real.log 181 ∧ Real.log 181 ≤ ((51984971/10000000):ℝ) := by
  apply dyadic_log_interval 181 ((75/256)) ((5198497/1000000)) ((51984971/10000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_182_interval : ((26020033/5000000):ℝ) ≤ Real.log 182 ∧ Real.log 182 ≤ ((52040067/10000000):ℝ) := by
  apply dyadic_log_interval 182 ((37/128)) ((26020033/5000000)) ((52040067/10000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_183_interval : ((52094861/10000000):ℝ) ≤ Real.log 183 ∧ Real.log 183 ≤ ((26047431/5000000):ℝ) := by
  apply dyadic_log_interval 183 ((73/256)) ((52094861/10000000)) ((26047431/5000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_184_interval : ((52149357/10000000):ℝ) ≤ Real.log 184 ∧ Real.log 184 ≤ ((26074679/5000000):ℝ) := by
  apply dyadic_log_interval 184 ((9/32)) ((52149357/10000000)) ((26074679/5000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_185_interval : ((26101779/5000000):ℝ) ≤ Real.log 185 ∧ Real.log 185 ≤ ((52203559/10000000):ℝ) := by
  apply dyadic_log_interval 185 ((71/256)) ((26101779/5000000)) ((52203559/10000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_186_interval : ((26128733/5000000):ℝ) ≤ Real.log 186 ∧ Real.log 186 ≤ ((52257467/10000000):ℝ) := by
  apply dyadic_log_interval 186 ((35/128)) ((26128733/5000000)) ((52257467/10000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_187_interval : ((26155543/5000000):ℝ) ≤ Real.log 187 ∧ Real.log 187 ≤ ((52311087/10000000):ℝ) := by
  apply dyadic_log_interval 187 ((69/256)) ((26155543/5000000)) ((52311087/10000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_188_interval : ((52364419/10000000):ℝ) ≤ Real.log 188 ∧ Real.log 188 ≤ ((2618221/500000):ℝ) := by
  apply dyadic_log_interval 188 ((17/64)) ((52364419/10000000)) ((2618221/500000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_189_interval : ((5241747/1000000):ℝ) ≤ Real.log 189 ∧ Real.log 189 ≤ ((52417471/10000000):ℝ) := by
  apply dyadic_log_interval 189 ((67/256)) ((5241747/1000000)) ((52417471/10000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_190_interval : ((327939/62500):ℝ) ≤ Real.log 190 ∧ Real.log 190 ≤ ((52470241/10000000):ℝ) := by
  apply dyadic_log_interval 190 ((33/128)) ((327939/62500)) ((52470241/10000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_191_interval : ((26261367/5000000):ℝ) ≤ Real.log 191 ∧ Real.log 191 ≤ ((10504547/2000000):ℝ) := by
  apply dyadic_log_interval 191 ((65/256)) ((26261367/5000000)) ((10504547/2000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_192_interval : ((52574953/10000000):ℝ) ≤ Real.log 192 ∧ Real.log 192 ≤ ((26287477/5000000):ℝ) := by
  apply dyadic_log_interval 192 ((1/4)) ((52574953/10000000)) ((26287477/5000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_193_interval : ((52626901/10000000):ℝ) ≤ Real.log 193 ∧ Real.log 193 ≤ ((26313451/5000000):ℝ) := by
  apply dyadic_log_interval 193 ((63/256)) ((52626901/10000000)) ((26313451/5000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_194_interval : ((52678581/10000000):ℝ) ≤ Real.log 194 ∧ Real.log 194 ≤ ((26339291/5000000):ℝ) := by
  apply dyadic_log_interval 194 ((31/128)) ((52678581/10000000)) ((26339291/5000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_195_interval : ((10545999/2000000):ℝ) ≤ Real.log 195 ∧ Real.log 195 ≤ ((13182499/2500000):ℝ) := by
  apply dyadic_log_interval 195 ((61/256)) ((10545999/2000000)) ((13182499/2500000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_196_interval : ((26390573/5000000):ℝ) ≤ Real.log 196 ∧ Real.log 196 ≤ ((52781147/10000000):ℝ) := by
  apply dyadic_log_interval 196 ((15/64)) ((26390573/5000000)) ((52781147/10000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_197_interval : ((52832037/10000000):ℝ) ≤ Real.log 197 ∧ Real.log 197 ≤ ((26416019/5000000):ℝ) := by
  apply dyadic_log_interval 197 ((59/256)) ((52832037/10000000)) ((26416019/5000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_198_interval : ((5288267/1000000):ℝ) ≤ Real.log 198 ∧ Real.log 198 ≤ ((52882671/10000000):ℝ) := by
  apply dyadic_log_interval 198 ((29/128)) ((5288267/1000000)) ((52882671/10000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_199_interval : ((6616631/1250000):ℝ) ≤ Real.log 199 ∧ Real.log 199 ≤ ((52933049/10000000):ℝ) := by
  apply dyadic_log_interval 199 ((57/256)) ((6616631/1250000)) ((52933049/10000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_200_interval : ((52983173/10000000):ℝ) ≤ Real.log 200 ∧ Real.log 200 ≤ ((26491587/5000000):ℝ) := by
  apply dyadic_log_interval 200 ((7/32)) ((52983173/10000000)) ((26491587/5000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_201_interval : ((53033049/10000000):ℝ) ≤ Real.log 201 ∧ Real.log 201 ≤ ((1060661/200000):ℝ) := by
  apply dyadic_log_interval 201 ((55/256)) ((53033049/10000000)) ((1060661/200000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_202_interval : ((13270669/2500000):ℝ) ≤ Real.log 202 ∧ Real.log 202 ≤ ((53082677/10000000):ℝ) := by
  apply dyadic_log_interval 202 ((27/128)) ((13270669/2500000)) ((53082677/10000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_203_interval : ((53132059/10000000):ℝ) ≤ Real.log 203 ∧ Real.log 203 ≤ ((2656603/500000):ℝ) := by
  apply dyadic_log_interval 203 ((53/256)) ((53132059/10000000)) ((2656603/500000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_204_interval : ((53181199/10000000):ℝ) ≤ Real.log 204 ∧ Real.log 204 ≤ ((132953/25000):ℝ) := by
  apply dyadic_log_interval 204 ((13/64)) ((53181199/10000000)) ((132953/25000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_205_interval : ((53230099/10000000):ℝ) ≤ Real.log 205 ∧ Real.log 205 ≤ ((532301/100000):ℝ) := by
  apply dyadic_log_interval 205 ((51/256)) ((53230099/10000000)) ((532301/100000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_206_interval : ((53278761/10000000):ℝ) ≤ Real.log 206 ∧ Real.log 206 ≤ ((26639381/5000000):ℝ) := by
  apply dyadic_log_interval 206 ((25/128)) ((53278761/10000000)) ((26639381/5000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_207_interval : ((53327187/10000000):ℝ) ≤ Real.log 207 ∧ Real.log 207 ≤ ((13331797/2500000):ℝ) := by
  apply dyadic_log_interval 207 ((49/256)) ((53327187/10000000)) ((13331797/2500000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_208_interval : ((2668769/500000):ℝ) ≤ Real.log 208 ∧ Real.log 208 ≤ ((53375381/10000000):ℝ) := by
  apply dyadic_log_interval 208 ((3/16)) ((2668769/500000)) ((53375381/10000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_209_interval : ((26711671/5000000):ℝ) ≤ Real.log 209 ∧ Real.log 209 ≤ ((53423343/10000000):ℝ) := by
  apply dyadic_log_interval 209 ((47/256)) ((26711671/5000000)) ((53423343/10000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_210_interval : ((2138843/400000):ℝ) ≤ Real.log 210 ∧ Real.log 210 ≤ ((13367769/2500000):ℝ) := by
  apply dyadic_log_interval 210 ((23/128)) ((2138843/400000)) ((13367769/2500000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_211_interval : ((53518581/10000000):ℝ) ≤ Real.log 211 ∧ Real.log 211 ≤ ((26759291/5000000):ℝ) := by
  apply dyadic_log_interval 211 ((45/256)) ((53518581/10000000)) ((26759291/5000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_212_interval : ((26782931/5000000):ℝ) ≤ Real.log 212 ∧ Real.log 212 ≤ ((53565863/10000000):ℝ) := by
  apply dyadic_log_interval 212 ((11/64)) ((26782931/5000000)) ((53565863/10000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_213_interval : ((53612921/10000000):ℝ) ≤ Real.log 213 ∧ Real.log 213 ≤ ((26806461/5000000):ℝ) := by
  apply dyadic_log_interval 213 ((43/256)) ((53612921/10000000)) ((26806461/5000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_214_interval : ((670747/125000):ℝ) ≤ Real.log 214 ∧ Real.log 214 ≤ ((53659761/10000000):ℝ) := by
  apply dyadic_log_interval 214 ((21/128)) ((670747/125000)) ((53659761/10000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_215_interval : ((2685319/500000):ℝ) ≤ Real.log 215 ∧ Real.log 215 ≤ ((53706381/10000000):ℝ) := by
  apply dyadic_log_interval 215 ((41/256)) ((2685319/500000)) ((53706381/10000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_216_interval : ((3359549/625000):ℝ) ≤ Real.log 216 ∧ Real.log 216 ≤ ((10750557/2000000):ℝ) := by
  apply dyadic_log_interval 216 ((5/32)) ((3359549/625000)) ((10750557/2000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_217_interval : ((53798973/10000000):ℝ) ≤ Real.log 217 ∧ Real.log 217 ≤ ((26899487/5000000):ℝ) := by
  apply dyadic_log_interval 217 ((39/256)) ((53798973/10000000)) ((26899487/5000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_218_interval : ((1076899/200000):ℝ) ≤ Real.log 218 ∧ Real.log 218 ≤ ((53844951/10000000):ℝ) := by
  apply dyadic_log_interval 218 ((19/128)) ((1076899/200000)) ((53844951/10000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_219_interval : ((53890717/10000000):ℝ) ≤ Real.log 219 ∧ Real.log 219 ≤ ((26945359/5000000):ℝ) := by
  apply dyadic_log_interval 219 ((37/256)) ((53890717/10000000)) ((26945359/5000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_220_interval : ((2157451/400000):ℝ) ≤ Real.log 220 ∧ Real.log 220 ≤ ((13484069/2500000):ℝ) := by
  apply dyadic_log_interval 220 ((9/64)) ((2157451/400000)) ((13484069/2500000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_221_interval : ((26990813/5000000):ℝ) ≤ Real.log 221 ∧ Real.log 221 ≤ ((13495407/2500000):ℝ) := by
  apply dyadic_log_interval 221 ((35/256)) ((26990813/5000000)) ((13495407/2500000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_222_interval : ((54026773/10000000):ℝ) ≤ Real.log 222 ∧ Real.log 222 ≤ ((27013387/5000000):ℝ) := by
  apply dyadic_log_interval 222 ((17/128)) ((54026773/10000000)) ((27013387/5000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_223_interval : ((54071717/10000000):ℝ) ≤ Real.log 223 ∧ Real.log 223 ≤ ((27035859/5000000):ℝ) := by
  apply dyadic_log_interval 223 ((33/256)) ((54071717/10000000)) ((27035859/5000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_224_interval : ((2705823/500000):ℝ) ≤ Real.log 224 ∧ Real.log 224 ≤ ((54116461/10000000):ℝ) := by
  apply dyadic_log_interval 224 ((1/8)) ((2705823/500000)) ((54116461/10000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_225_interval : ((13540251/2500000):ℝ) ≤ Real.log 225 ∧ Real.log 225 ≤ ((10832201/2000000):ℝ) := by
  apply dyadic_log_interval 225 ((31/256)) ((13540251/2500000)) ((10832201/2000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_226_interval : ((54205349/10000000):ℝ) ≤ Real.log 226 ∧ Real.log 226 ≤ ((54205351/10000000):ℝ) := by
  apply dyadic_log_interval 226 ((15/128)) ((54205349/10000000)) ((54205351/10000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_227_interval : ((108499/20000):ℝ) ≤ Real.log 227 ∧ Real.log 227 ≤ ((54249501/10000000):ℝ) := by
  apply dyadic_log_interval 227 ((29/256)) ((108499/20000)) ((54249501/10000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_228_interval : ((3393341/625000):ℝ) ≤ Real.log 228 ∧ Real.log 228 ≤ ((54293457/10000000):ℝ) := by
  apply dyadic_log_interval 228 ((7/64)) ((3393341/625000)) ((54293457/10000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_229_interval : ((2716861/500000):ℝ) ≤ Real.log 229 ∧ Real.log 229 ≤ ((54337221/10000000):ℝ) := by
  apply dyadic_log_interval 229 ((27/256)) ((2716861/500000)) ((54337221/10000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_230_interval : ((54380793/10000000):ℝ) ≤ Real.log 230 ∧ Real.log 230 ≤ ((27190397/5000000):ℝ) := by
  apply dyadic_log_interval 230 ((13/128)) ((54380793/10000000)) ((27190397/5000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_231_interval : ((54424177/10000000):ℝ) ≤ Real.log 231 ∧ Real.log 231 ≤ ((27212089/5000000):ℝ) := by
  apply dyadic_log_interval 231 ((25/256)) ((54424177/10000000)) ((27212089/5000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_232_interval : ((54467373/10000000):ℝ) ≤ Real.log 232 ∧ Real.log 232 ≤ ((27233687/5000000):ℝ) := by
  apply dyadic_log_interval 232 ((3/32)) ((54467373/10000000)) ((27233687/5000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_233_interval : ((3406899/625000):ℝ) ≤ Real.log 233 ∧ Real.log 233 ≤ ((10902077/2000000):ℝ) := by
  apply dyadic_log_interval 233 ((23/256)) ((3406899/625000)) ((10902077/2000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_234_interval : ((54553211/10000000):ℝ) ≤ Real.log 234 ∧ Real.log 234 ≤ ((13638303/2500000):ℝ) := by
  apply dyadic_log_interval 234 ((11/128)) ((54553211/10000000)) ((13638303/2500000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_235_interval : ((10919171/2000000):ℝ) ≤ Real.log 235 ∧ Real.log 235 ≤ ((3412241/625000):ℝ) := by
  apply dyadic_log_interval 235 ((21/256)) ((10919171/2000000)) ((3412241/625000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_236_interval : ((27319159/5000000):ℝ) ≤ Real.log 236 ∧ Real.log 236 ≤ ((54638319/10000000):ℝ) := by
  apply dyadic_log_interval 236 ((5/64)) ((27319159/5000000)) ((54638319/10000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_237_interval : ((54680601/10000000):ℝ) ≤ Real.log 237 ∧ Real.log 237 ≤ ((27340301/5000000):ℝ) := by
  apply dyadic_log_interval 237 ((19/256)) ((54680601/10000000)) ((27340301/5000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_238_interval : ((27361353/5000000):ℝ) ≤ Real.log 238 ∧ Real.log 238 ≤ ((54722707/10000000):ℝ) := by
  apply dyadic_log_interval 238 ((9/128)) ((27361353/5000000)) ((54722707/10000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_239_interval : ((10952927/2000000):ℝ) ≤ Real.log 239 ∧ Real.log 239 ≤ ((13691159/2500000):ℝ) := by
  apply dyadic_log_interval 239 ((17/256)) ((10952927/2000000)) ((13691159/2500000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_240_interval : ((54806389/10000000):ℝ) ≤ Real.log 240 ∧ Real.log 240 ≤ ((5480639/1000000):ℝ) := by
  apply dyadic_log_interval 240 ((1/16)) ((54806389/10000000)) ((5480639/1000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_241_interval : ((54847969/10000000):ℝ) ≤ Real.log 241 ∧ Real.log 241 ≤ ((5484797/1000000):ℝ) := by
  apply dyadic_log_interval 241 ((15/256)) ((54847969/10000000)) ((5484797/1000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_242_interval : ((54889377/10000000):ℝ) ≤ Real.log 242 ∧ Real.log 242 ≤ ((27444689/5000000):ℝ) := by
  apply dyadic_log_interval 242 ((7/128)) ((54889377/10000000)) ((27444689/5000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_243_interval : ((27465307/5000000):ℝ) ≤ Real.log 243 ∧ Real.log 243 ≤ ((10986123/2000000):ℝ) := by
  apply dyadic_log_interval 243 ((13/256)) ((27465307/5000000)) ((10986123/2000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_244_interval : ((27485841/5000000):ℝ) ≤ Real.log 244 ∧ Real.log 244 ≤ ((54971683/10000000):ℝ) := by
  apply dyadic_log_interval 244 ((3/64)) ((27485841/5000000)) ((54971683/10000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_245_interval : ((27506291/5000000):ℝ) ≤ Real.log 245 ∧ Real.log 245 ≤ ((55012583/10000000):ℝ) := by
  apply dyadic_log_interval 245 ((11/256)) ((27506291/5000000)) ((55012583/10000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_246_interval : ((11010663/2000000):ℝ) ≤ Real.log 246 ∧ Real.log 246 ≤ ((13763329/2500000):ℝ) := by
  apply dyadic_log_interval 246 ((5/128)) ((11010663/2000000)) ((13763329/2500000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_247_interval : ((55093883/10000000):ℝ) ≤ Real.log 247 ∧ Real.log 247 ≤ ((13773471/2500000):ℝ) := by
  apply dyadic_log_interval 247 ((9/256)) ((55093883/10000000)) ((13773471/2500000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_248_interval : ((55134287/10000000):ℝ) ≤ Real.log 248 ∧ Real.log 248 ≤ ((3445893/625000):ℝ) := by
  apply dyadic_log_interval 248 ((1/32)) ((55134287/10000000)) ((3445893/625000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_249_interval : ((431051/78125):ℝ) ≤ Real.log 249 ∧ Real.log 249 ≤ ((55174529/10000000):ℝ) := by
  apply dyadic_log_interval 249 ((7/256)) ((431051/78125)) ((55174529/10000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_250_interval : ((55214609/10000000):ℝ) ≤ Real.log 250 ∧ Real.log 250 ≤ ((5521461/1000000):ℝ) := by
  apply dyadic_log_interval 250 ((3/128)) ((55214609/10000000)) ((5521461/1000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_251_interval : ((55254529/10000000):ℝ) ≤ Real.log 251 ∧ Real.log 251 ≤ ((5525453/1000000):ℝ) := by
  apply dyadic_log_interval 251 ((5/256)) ((55254529/10000000)) ((5525453/1000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_252_interval : ((5529429/1000000):ℝ) ≤ Real.log 252 ∧ Real.log 252 ≤ ((55294291/10000000):ℝ) := by
  apply dyadic_log_interval 252 ((1/64)) ((5529429/1000000)) ((55294291/10000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_253_interval : ((27666947/5000000):ℝ) ≤ Real.log 253 ∧ Real.log 253 ≤ ((11066779/2000000):ℝ) := by
  apply dyadic_log_interval 253 ((3/256)) ((27666947/5000000)) ((11066779/2000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_254_interval : ((27686671/5000000):ℝ) ≤ Real.log 254 ∧ Real.log 254 ≤ ((55373343/10000000):ℝ) := by
  apply dyadic_log_interval 254 ((1/128)) ((27686671/5000000)) ((55373343/10000000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_255_interval : ((11082527/2000000):ℝ) ≤ Real.log 255 ∧ Real.log 255 ≤ ((13853159/2500000):ℝ) := by
  apply dyadic_log_interval 255 ((1/256)) ((11082527/2000000)) ((13853159/2500000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_256_interval : ((27725887/5000000):ℝ) ≤ Real.log 256 ∧ Real.log 256 ≤ ((2218071/400000):ℝ) := by
  apply dyadic_log_interval 256 (0) ((27725887/5000000)) ((2218071/400000)) 8 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_257_interval : ((867043/156250):ℝ) ≤ Real.log 257 ∧ Real.log 257 ≤ ((55490771/10000000):ℝ) := by
  apply dyadic_log_interval 257 ((255/512)) ((867043/156250)) ((55490771/10000000)) 9 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

end AgentUCTRealIndex
