import BookRamsey.R47.Step_d10_Cubes
import BookRamsey.R47.Step_d10_Coverage
import BookRamsey.RowBridge

namespace BookRamsey.R47

open BookRamsey

set_option maxHeartbeats 0 in
theorem exclude_d10 :
    ∀ red : Fin 22 → Fin 22 → Bool,
      Symm red → BookFree red 4 7 →
      (∀ w : Fin 22, 7 ≤ redDeg red w ∧ redDeg red w ≤ 10) →
      ∀ v : Fin 22, redDeg red v ≠ 10 := by
  have hunit : ∀ c ∈ cubes_d10,
      (rcnf 22 4 7 10 7 10 ++ unitsOf c).Unsat := by
    intro c hc
    unfold cubes_d10 at hc
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_requeue_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, false), (56, true), (34, true), (69, true), (59, false), (50, true), (35, false), (82, true), (95, false), (1847, false), (126, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_requeue_b001_batch0_unsat [(22, true), (41, false), (64, false), (42, true), (82, false), (599, true), (1902, true), (1811, false), (78, false), (36, true), (95, false), (2000, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_requeue_b001_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, false), (99, false), (1905, true), (35, false), (56, true), (34, true), (50, true), (44, true), (61, true), (98, true), (63, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_requeue_b001_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, true), (98, false), (44, false), (96, false), (35, false), (55, true), (34, true), (50, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_requeue_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, false), (1820, false), (311, false), (95, false), (34, true), (50, false), (88, false), (35, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_requeue_b001_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, true), (98, false), (44, true), (35, false), (56, true), (34, true), (50, true), (70, true), (85, false), (87, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_requeue_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, false), (1820, false), (311, false), (95, false), (34, true), (50, false), (88, false), (35, false), (49, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_requeue_b002_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, true), (98, false), (44, true), (35, false), (56, true), (34, true), (50, true), (70, true), (85, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_requeue_b002_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, false), (56, true), (34, true), (69, true), (59, false), (50, true), (35, false), (82, true), (95, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_requeue_b002_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, false), (1820, false), (311, false), (95, false), (34, false), (54, true), (58, false), (112, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, false), (1820, false), (311, false), (95, false), (34, false), (54, true), (58, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, false), (56, true), (34, false), (58, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, true), (60, false), (1836, false), (99, true), (112, false), (1910, true), (34, false), (58, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, true), (1846, false), (83, true), (56, true), (34, false), (58, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, false), (56, false), (34, false), (53, false), (2339, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, true), (60, false), (1836, false), (99, false), (1840, true), (34, true), (87, false), (2065, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, true), (60, false), (1836, false), (99, true), (112, true), (1878, true), (126, true), (33, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, false), (42, true), (82, true), (126, true), (1878, true), (284, true), (599, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, true), (1846, false), (83, true), (56, false), (35, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, false), (99, false), (95, false), (36, false), (81, true), (111, false), (49, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, false), (99, true), (36, false), (35, true), (50, true), (392, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, true), (60, false), (1836, false), (99, true), (112, true), (1878, true), (126, false), (33, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, true), (60, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, false), (99, false), (95, false), (36, false), (81, true), (111, true), (114, false), (1847, true), (57152, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, false), (99, false), (95, false), (36, false), (81, true), (111, true), (114, false), (1847, true), (57152, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, false), (99, false), (95, false), (36, false), (81, true), (111, true), (114, true), (49, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, false), (99, false), (95, false), (36, false), (81, true), (111, false), (49, true), (97, true), (126, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, false), (99, false), (95, false), (36, false), (81, true), (111, true), (114, false), (1847, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, false), (99, true), (36, false), (35, true), (50, true), (392, false), (526, true), (74, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, false), (99, false), (1905, false), (34, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, false), (99, false), (95, false), (36, false), (81, false), (98, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, false), (99, true), (36, false), (35, true), (50, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, false), (99, false), (1905, false), (34, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, false), (113, true), (1914, true), (56, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, false), (99, false), (95, false), (36, false), (81, true), (111, true), (114, true), (49, true), (35, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, true), (60, false), (1836, false), (99, false), (1840, false), (112, false), (126, true), (35, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, true), (60, false), (1836, true), (42, true), (1909, true), (97, false), (113, true), (2929, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, false), (113, false), (391, true), (57, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, false), (99, false), (95, false), (36, false), (81, true), (111, true), (114, true), (49, true), (35, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, false), (42, true), (82, true), (126, true), (1878, false), (599, true), (36, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, false), (113, false), (391, true), (57, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, false), (99, true), (36, false), (35, true), (50, true), (392, false), (526, true), (74, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, false), (99, false), (95, false), (36, false), (81, false), (98, false), (114, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, false), (99, false), (95, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, true), (1846, true), (1904, true), (95, true), (82, false), (1921, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, true), (60, false), (1836, true), (42, false), (98, false), (1907, false), (61, true), (55, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, true), (60, false), (1836, false), (99, true), (112, true), (1878, false), (140, true), (35, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, true), (60, false), (1836, false), (99, false), (1840, false), (112, false), (126, true), (35, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, false), (99, true), (36, false), (35, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, false), (99, true), (36, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, false), (99, false), (95, false), (36, true), (76, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, true), (60, false), (1836, false), (99, true), (112, false), (1910, false), (1879, true), (153, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, true), (1846, true), (1904, true), (95, true), (82, false), (1921, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, false), (99, false), (95, false), (36, false), (81, true), (111, false), (49, true), (97, true), (126, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, false), (1820, false), (311, false), (95, false), (34, false), (54, true), (58, false), (112, true), (114, true), (153, false), (127, false), (141, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, true), (1846, true), (1904, false), (56, false), (35, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, true), (60, false), (1836, true), (42, true), (1909, false), (126, true), (140, true), (2355, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, false), (1820, false), (311, false), (95, false), (34, false), (54, true), (58, false), (112, true), (114, true), (153, false), (127, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, true), (60, false), (1836, false), (99, false), (1840, false), (112, true), (34, false), (54, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, false), (42, true), (82, true), (126, true), (1878, false), (599, false), (57, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, false), (42, true), (82, false), (599, true), (1902, false), (43, false), (140, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, true), (60, false), (1836, true), (42, true), (1909, true), (97, true), (112, true), (1879, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, true), (60, false), (1836, true), (42, true), (1909, false), (126, true), (140, false), (153, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, true), (1846, false), (83, false), (56, false), (2745, true), (2920, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, true), (1846, false), (83, true), (56, true), (34, false), (58, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, true), (1846, true), (1904, true), (95, true), (82, true), (56, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, true), (60, false), (1836, true), (42, true), (1909, false), (126, false), (153, true), (1916, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, false), (42, true), (82, true), (126, true), (1878, true), (284, true), (599, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, true), (1846, true), (1904, false), (56, true), (34, false), (140, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, true), (60, false), (1836, false), (99, true), (112, false), (1910, false), (1879, true), (153, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, false), (99, false), (95, false), (36, false), (81, false), (98, false), (114, false), (78, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, true), (1846, false), (83, false), (56, false), (2745, true), (2920, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, true), (60, false), (1836, false), (99, true), (112, true), (1878, true), (126, true), (33, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, true), (1846, false), (83, false), (56, false), (2745, false), (91, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, true), (60, false), (1836, true), (42, true), (1909, false), (126, false), (153, true), (1916, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, false), (99, false), (95, false), (36, false), (81, false), (98, false), (114, false), (78, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, true), (1846, false), (83, false), (56, true), (34, false), (217, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, false), (56, false), (34, false), (53, true), (1835, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, true), (1846, true), (1904, true), (95, true), (82, true), (56, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, true), (60, false), (1836, true), (42, true), (1909, true), (97, false), (113, false), (1879, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, false), (99, false), (95, false), (36, true), (76, false), (111, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, true), (98, true), (3751, true), (44, true), (1871, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, true), (1846, true), (1904, false), (56, true), (34, false), (140, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, true), (60, false), (1836, true), (42, true), (1909, true), (97, false), (113, false), (1879, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, true), (1846, false), (83, false), (56, false), (2745, false), (91, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, true), (1846, false), (83, false), (56, true), (34, false), (217, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, true), (1846, false), (83, false), (56, true), (34, true), (599, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, false), (99, false), (95, false), (36, true), (76, false), (111, false), (97, false), (604, false), (107, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, true), (1846, false), (83, true), (56, false), (35, false), (2745, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, true), (60, false), (1836, true), (42, true), (1909, false), (126, true), (140, false), (153, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, false), (99, false), (95, false), (36, true), (76, false), (111, false), (97, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, true), (60, false), (1836, true), (42, false), (98, false), (1907, false), (61, true), (55, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, true), (1846, false), (83, true), (56, true), (34, true), (599, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, true), (60, false), (1836, false), (99, true), (112, true), (1878, true), (126, false), (33, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, false), (99, true), (36, false), (35, true), (50, true), (392, false), (526, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, false), (42, true), (82, true), (126, true), (1878, false), (599, true), (36, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, true), (1846, false), (83, true), (56, false), (35, false), (2745, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, true), (60, false), (1836, true), (42, true), (1909, false), (126, false), (153, false), (3170, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, false), (99, false), (95, false), (36, false), (81, true), (111, false), (49, true), (97, false), (1847, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, true), (60, false), (1836, true), (42, true), (1909, false), (126, true), (140, true), (2355, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, true), (60, false), (1836, true), (42, true), (1909, false), (126, false), (153, false), (3170, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, true), (140, false), (311, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, false), (42, true), (82, false), (599, false), (1902, false), (43, false), (140, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, false), (42, true), (82, true), (126, false), (599, false), (98, true), (113, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, true), (60, false), (1836, true), (42, true), (1909, true), (97, true), (112, false), (126, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, false), (99, false), (95, false), (36, true), (76, false), (111, false), (97, false), (604, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, true), (1846, false), (83, true), (56, true), (34, true), (599, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, false), (99, false), (95, false), (36, false), (81, true), (111, false), (49, true), (97, false), (1847, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, true), (1846, true), (1904, false), (56, false), (35, false), (2745, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, true), (60, false), (1836, false), (99, false), (1840, false), (112, true), (34, true), (87, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, true), (98, true), (3751, false), (44, true), (347, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, true), (60, false), (1836, true), (42, true), (1909, true), (97, false), (113, true), (2929, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, true), (60, false), (1836, true), (42, true), (1909, true), (97, true), (112, true), (1879, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, false), (42, true), (82, false), (599, false), (1902, true), (1811, false), (95, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, true), (60, false), (1836, true), (42, false), (98, true), (78, true), (35, true), (126, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, false), (42, true), (82, false), (599, false), (1902, false), (43, false), (140, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, false), (56, true), (34, false), (58, false), (1835, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, false), (99, false), (95, false), (36, true), (76, false), (111, false), (97, false), (604, false), (107, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, true), (98, true), (3751, false), (44, false), (347, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, false), (42, true), (82, true), (126, false), (599, true), (36, false), (98, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, false), (42, true), (82, true), (126, false), (599, false), (98, true), (113, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, true), (60, false), (1836, false), (99, false), (1840, false), (112, true), (34, true), (87, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, false), (42, true), (82, true), (126, false), (599, true), (36, true), (98, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, false), (42, true), (82, true), (126, true), (1878, false), (599, false), (57, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, true), (1846, false), (83, false), (56, true), (34, true), (599, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, true), (98, false), (44, false), (96, true), (126, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, false), (113, true), (1914, true), (56, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, true), (60, false), (1836, true), (42, false), (98, false), (1907, true), (43, false), (33, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, true), (60, false), (1836, true), (42, false), (98, true), (78, true), (35, true), (126, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, false), (1820, true), (140, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, false), (42, true), (82, false), (599, true), (1902, false), (43, false), (140, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, true), (1846, true), (1904, false), (56, false), (35, false), (2745, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, true), (60, false), (1836, true), (42, false), (98, false), (1907, true), (43, false), (33, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, true), (140, true), (56, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, true), (60, false), (1836, false), (99, true), (112, false), (1910, false), (1879, false), (1914, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, true), (140, true), (56, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, true), (60, false), (1836, true), (42, true), (1909, true), (97, true), (112, false), (126, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, false), (1820, false), (311, false), (95, false), (34, true), (50, false), (88, false), (35, false), (49, true), (56, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, true), (60, false), (1836, false), (99, false), (1840, false), (112, true), (34, false), (54, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, true), (60, false), (1836, true), (42, false), (98, true), (78, true), (35, false), (126, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, false), (113, true), (1914, false), (311, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, true), (60, false), (1836, false), (99, false), (1840, true), (34, false), (54, true), (126, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, false), (113, true), (1914, false), (311, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, false), (99, true), (62, false), (55, true), (113, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, true), (1846, true), (1904, false), (56, true), (34, true), (599, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, false), (42, true), (82, false), (599, false), (1902, false), (43, true), (1908, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, true), (1846, true), (1904, false), (56, true), (34, true), (599, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, true), (60, false), (1836, false), (99, true), (112, true), (1878, false), (140, false), (35, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, false), (56, false), (34, false), (53, false), (2339, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, false), (1820, false), (311, false), (95, false), (34, true), (50, false), (88, false), (35, false), (49, true), (56, true), (112, true), (114, true), (153, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, true), (60, false), (1836, false), (99, true), (112, true), (1878, false), (140, true), (35, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, false), (1820, false), (311, false), (95, false), (34, false), (54, true), (58, false), (112, true), (114, true), (153, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, false), (1820, false), (311, false), (95, false), (34, true), (50, false), (88, false), (35, false), (49, true), (56, true), (112, true), (114, true), (153, false), (127, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, false), (99, true), (62, false), (55, false), (76, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, true), (98, true), (3751, false), (44, true), (347, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, false), (56, false), (34, false), (53, true), (1835, true), (76, false), (49, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, true), (98, true), (3751, true), (44, false), (1872, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, true), (60, false), (1836, true), (42, false), (98, true), (78, false), (113, true), (1879, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, false), (42, true), (82, true), (126, false), (599, false), (98, false), (284, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, true), (98, true), (3751, false), (44, false), (347, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, true), (60, false), (1836, true), (42, false), (98, true), (78, true), (35, false), (126, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, false), (99, true), (62, false), (55, true), (113, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, false), (99, true), (62, false), (55, false), (76, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, false), (42, true), (82, false), (599, false), (1902, true), (1811, true), (81, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, false), (99, true), (62, true), (1908, false), (1811, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, false), (56, false), (34, true), (599, true), (2000, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, false), (113, false), (391, false), (1914, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, true), (98, false), (44, false), (96, false), (35, false), (55, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, true), (60, false), (1836, true), (42, false), (98, false), (1907, false), (61, false), (1914, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, false), (1820, false), (311, false), (95, false), (34, true), (50, true), (69, true), (35, false), (112, true), (114, true), (153, false), (127, false), (141, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, false), (42, true), (82, true), (126, true), (1878, true), (284, false), (599, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, true), (60, false), (1836, false), (99, false), (1840, true), (34, false), (54, false), (75, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, false), (1820, false), (311, false), (95, false), (34, true), (50, true), (69, true), (35, false), (112, true), (114, true), (153, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, false), (42, true), (82, false), (599, true), (1902, false), (43, true), (1908, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, true), (60, false), (1836, false), (99, false), (1840, true), (34, true), (87, true), (35, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, true), (98, false), (44, true), (35, false), (56, false), (34, false), (54, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, true), (98, false), (44, true), (35, false), (56, true), (34, true), (50, true), (70, true), (85, false), (87, false), (95, false), (113, true), (140, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, false), (56, false), (34, false), (53, true), (1835, true), (76, false), (49, true), (93, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, true), (60, false), (1836, true), (42, false), (98, false), (1907, true), (43, true), (34, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, false), (1820, false), (311, false), (95, false), (34, true), (50, true), (69, true), (35, false), (112, true), (114, true), (153, false), (127, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, true), (60, false), (1836, false), (99, false), (1840, false), (112, false), (126, false), (1910, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, true), (98, false), (44, true), (35, false), (56, true), (34, true), (50, true), (70, true), (85, false), (87, false), (95, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, true), (60, false), (1836, false), (99, true), (112, true), (1878, false), (140, false), (35, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, true), (60, false), (1836, false), (99, false), (1840, false), (112, false), (126, false), (1910, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, false), (1820, false), (311, false), (95, false), (34, false), (54, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b001_batch0_unsat [(22, true), (41, true), (60, false), (1836, true), (42, false), (98, false), (1907, false), (61, false), (1914, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b002_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, false), (56, true), (34, true), (69, false), (82, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b002_batch0_unsat [(22, true), (41, false), (64, false), (42, true), (82, false), (599, false), (1902, true), (1811, true), (81, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b002_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, false), (56, false), (34, false), (53, true), (1835, true), (76, false), (49, true), (93, true), (95, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b002_batch0_unsat [(22, true), (41, true), (60, false), (1836, false), (99, false), (1840, true), (34, false), (54, false), (75, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b002_batch0_unsat [(22, true), (41, false), (64, true), (111, true), (1846, true), (1904, true), (95, false), (83, false), (1911, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b002_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, true), (98, false), (44, true), (35, true), (88, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b002_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, false), (99, false), (1905, true), (35, true), (61, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b002_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, true), (98, false), (44, false), (96, true), (126, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b002_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, true), (98, true), (3751, true), (44, false), (1872, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b002_batch0_unsat [(22, true), (41, false), (64, false), (42, true), (82, true), (126, false), (599, false), (98, false), (284, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b002_batch0_unsat [(22, true), (41, true), (60, false), (1836, false), (99, true), (112, false), (1910, true), (34, true), (87, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b002_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, false), (99, true), (62, true), (1908, false), (1811, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b002_batch0_unsat [(22, true), (41, true), (60, false), (1836, true), (42, false), (98, true), (78, false), (113, true), (1879, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b003_batch0_unsat [(22, true), (41, true), (60, false), (1836, false), (99, true), (112, false), (1910, false), (1879, false), (1914, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b003_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, false), (113, false), (391, false), (1914, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b003_batch0_unsat [(22, true), (41, true), (60, false), (1836, true), (42, false), (98, true), (78, false), (113, false), (33, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b003_batch0_unsat [(22, true), (41, false), (64, false), (42, true), (82, false), (599, true), (1902, true), (1811, false), (78, false), (36, true), (95, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b003_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, false), (56, true), (34, true), (69, true), (59, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b003_batch0_unsat [(22, true), (41, false), (64, false), (42, true), (82, true), (126, true), (1878, true), (284, false), (599, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b003_batch0_unsat [(22, true), (41, false), (64, true), (111, true), (1846, true), (1904, true), (95, false), (83, true), (1911, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b004_batch0_unsat [(22, true), (41, false), (64, false), (42, true), (82, true), (126, false), (599, true), (36, false), (98, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b004_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, false), (1820, false), (311, false), (95, false), (34, true), (50, false), (88, false), (35, false), (49, true), (56, true), (112, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b004_batch0_unsat [(22, true), (41, false), (64, false), (42, true), (82, false), (599, true), (1902, true), (1811, false), (78, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b004_batch0_unsat [(22, true), (41, true), (60, false), (1836, false), (99, true), (112, false), (1910, true), (34, true), (87, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b005_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, false), (1820, true), (140, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b005_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, false), (56, false), (34, true), (599, false), (693, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b005_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, false), (99, false), (1905, true), (35, false), (56, true), (34, true), (50, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b006_batch0_unsat [(22, true), (41, false), (64, false), (42, true), (82, false), (599, true), (1902, true), (1811, true), (81, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b006_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, false), (1820, false), (311, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b007_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, false), (56, false), (34, true), (599, true), (2000, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b007_batch0_unsat [(22, true), (41, false), (64, false), (42, true), (82, false), (599, false), (1902, false), (43, true), (1908, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b008_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, false), (99, false), (1905, true), (35, false), (56, true), (34, false), (69, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b008_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, false), (56, false), (34, true), (599, false), (693, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b009_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, false), (1820, false), (311, false), (95, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b009_batch0_unsat [(22, true), (41, true), (60, false), (1836, true), (42, false), (98, true), (78, false), (113, false), (33, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b010_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, false), (99, false), (1905, true), (35, false), (56, true), (34, false), (69, true), (68, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b010_batch0_unsat [(22, true), (41, true), (60, false), (1836, false), (99, false), (1840, true), (34, true), (87, false), (2065, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b011_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, true), (98, false), (44, false), (96, false), (35, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b011_batch0_unsat [(22, true), (41, true), (60, false), (1836, true), (42, false), (98, false), (1907, true), (43, true), (34, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b012_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, false), (99, true), (62, true), (1908, true), (1811, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b013_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, false), (56, true), (34, true), (69, true), (59, false), (50, true), (35, false), (82, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b014_batch0_unsat [(22, true), (41, true), (60, false), (1836, false), (99, true), (112, false), (1910, true), (34, false), (58, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b015_batch0_unsat [(22, true), (41, false), (64, false), (42, true), (82, true), (126, false), (599, true), (36, true), (98, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b016_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, true), (98, true), (3751, true), (44, true), (1871, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b017_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, false), (1820, false), (311, false), (95, false), (34, true), (50, false), (88, false), (35, false), (49, true), (56, true), (112, true), (114, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b018_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, false), (99, false), (1905, true), (35, true), (61, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b019_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, false), (99, false), (1905, true), (35, false), (56, true), (34, true), (50, true), (44, true), (61, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b020_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, false), (99, false), (1905, true), (35, false), (56, true), (34, true), (50, true), (44, true), (61, true), (98, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b021_batch0_unsat [(22, true), (41, false), (64, false), (42, true), (82, false), (599, true), (1902, true), (1811, true), (81, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b022_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, false), (1820, false), (311, false), (95, false), (34, false), (54, true), (58, false), (112, true), (114, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b023_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, true), (98, false), (44, true), (35, false), (56, true), (34, true), (50, true), (70, true), (85, false), (87, false), (95, false), (113, true), (140, false), (111, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b024_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, true), (98, false), (44, false), (96, false), (35, false), (55, true), (34, false), (127, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b025_batch0_unsat [(22, true), (41, false), (64, true), (111, true), (1846, true), (1904, true), (95, false), (83, false), (1911, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b026_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, false), (1820, false), (311, false), (95, false), (34, true), (50, true), (69, true), (35, true), (89, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b027_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, true), (98, false), (44, true), (35, false), (56, true), (34, true), (50, true), (70, false), (88, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b028_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, false), (56, true), (34, true), (69, true), (59, false), (50, true), (35, true), (70, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b029_batch0_unsat [(22, true), (41, true), (60, false), (1836, false), (99, false), (1840, true), (34, true), (87, true), (35, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b030_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, true), (98, false), (44, true), (35, false), (56, true), (34, true), (50, true), (70, false), (88, false), (93, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b031_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, false), (99, true), (62, true), (1908, true), (1811, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b032_batch0_unsat [(22, true), (41, false), (64, false), (42, true), (82, false), (599, false), (1902, true), (1811, false), (95, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b033_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, true), (98, false), (44, true), (35, false), (56, false), (34, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b034_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, true), (98, false), (44, true), (35, false), (56, true), (34, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b035_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, false), (1820, false), (311, false), (95, false), (34, true), (50, false), (88, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b036_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, true), (98, false), (44, true), (35, false), (56, false), (34, false), (54, true), (76, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b037_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, false), (56, true), (34, true), (69, false), (82, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b038_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, false), (1820, false), (311, false), (95, false), (34, true), (50, true), (69, true), (35, false), (112, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b039_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, false), (56, false), (34, false), (53, true), (1835, true), (76, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_b040_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, false), (1820, false), (311, false), (95, false), (34, true), (50, true), (69, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_requeue_b003_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, true), (98, false), (44, true), (35, false), (56, true), (34, true), (50, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_requeue_b004_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, true), (98, false), (44, false), (96, false), (35, false), (55, true), (34, false), (127, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_requeue_b005_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, false), (56, true), (34, true), (69, true), (59, false), (50, true), (35, true), (70, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_requeue_b006_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, false), (56, true), (34, true), (69, true), (59, false), (50, true), (35, false), (82, true), (95, false), (1847, false), (126, false), (99, true), (97, false), (80, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_requeue_b007_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, true), (98, false), (44, false), (96, false), (35, false), (55, true), (34, true), (50, true), (67, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_requeue_b008_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, false), (1820, false), (311, false), (95, false), (34, false), (54, true), (58, false), (112, true), (114, true), (153, false), (127, false), (141, false), (50, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_requeue_b009_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, false), (56, true), (34, true), (69, true), (59, false), (50, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_requeue_b010_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, false), (56, true), (34, true), (69, true), (59, false), (50, true), (35, false), (82, true), (95, false), (1847, false), (126, false), (99, false), (141, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_requeue_b011_batch0_unsat [(22, true), (41, false), (64, false), (42, true), (82, false), (599, true), (1902, true), (1811, false), (78, false), (36, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_requeue_b012_batch0_unsat [(22, true), (41, false), (64, false), (42, true), (82, false), (599, true), (1902, false), (43, true), (1908, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_requeue_b013_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, false), (56, true), (34, false), (58, false), (1835, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_requeue_b014_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, false), (56, true), (34, true), (69, true), (59, false), (50, true), (35, false), (82, true), (95, false), (1847, false), (126, false), (99, true), (97, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_requeue_b015_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, true), (98, false), (44, true), (35, true), (88, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_requeue_b016_batch0_unsat [(22, true), (41, true), (60, false), (1836, false), (99, false), (1840, true), (34, false), (54, true), (126, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_requeue_b017_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, true), (98, false), (44, false), (96, false), (35, false), (55, true), (34, true), (50, true), (67, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_requeue_b018_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, true), (98, false), (44, true), (35, false), (56, false), (34, false), (54, true), (76, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_requeue_b020_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, false), (56, true), (34, true), (69, true), (59, false), (50, true), (35, false), (82, true), (95, false), (1847, false), (126, false), (99, false), (141, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_requeue_b022_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, false), (56, true), (34, true), (69, true), (59, false), (50, true), (35, false), (82, true), (95, false), (1847, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_requeue_b024_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, false), (56, false), (34, false), (53, true), (1835, true), (76, false), (49, true), (93, true), (95, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_requeue_b025_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, false), (99, false), (1905, true), (35, false), (56, true), (34, true), (50, true), (44, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_requeue_b026_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, true), (140, false), (311, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_requeue_b027_batch0_unsat [(22, true), (41, false), (64, true), (111, true), (1846, true), (1904, true), (95, false), (83, true), (1911, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_requeue_b028_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, false), (99, false), (1905, true), (35, false), (56, true), (34, false), (69, true), (68, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_requeue_b029_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, false), (99, false), (1905, true), (35, false), (56, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_requeue_b032_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, true), (98, false), (44, true), (35, false), (56, true), (34, true), (50, true), (70, false), (88, false), (93, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_requeue_b033_batch0_unsat [(22, true), (41, false), (64, false), (42, true), (82, false), (599, true), (1902, true), (1811, false), (78, false), (36, true), (95, false), (2000, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_requeue_b034_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, false), (56, true), (34, true), (69, true), (59, false), (50, true), (35, false), (82, true), (95, false), (1847, false), (126, false), (99, true), (97, false), (80, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_requeue_b035_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, false), (1820, false), (311, false), (95, false), (34, true), (50, true), (69, true), (35, true), (89, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_requeue_b036_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, true), (98, false), (44, true), (35, false), (56, true), (34, true), (50, true), (70, true), (85, false), (87, false), (95, false), (113, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_requeue_b037_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, false), (99, false), (1905, true), (35, false), (56, true), (34, true), (50, true), (44, true), (61, true), (98, true), (63, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_requeue_b038_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, false), (1820, false), (311, false), (95, false), (34, true), (50, true), (69, true), (35, false), (112, true), (114, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_tail_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, false), (1820, false), (311, false), (95, false), (34, true), (50, true), (69, true), (35, false), (112, true), (114, true), (153, false), (127, false), (141, false), (70, true), (85, false), (87, false), (55, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_tail_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, false), (1820, false), (311, false), (95, false), (34, false), (54, true), (58, false), (112, true), (114, true), (153, false), (127, false), (141, false), (50, true), (57113, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_tail_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, false), (1820, false), (311, false), (95, false), (34, true), (50, true), (69, true), (35, false), (112, true), (114, true), (153, false), (127, false), (141, false), (70, true), (85, false), (87, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_tail_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, false), (1820, false), (311, false), (95, false), (34, true), (50, true), (69, true), (35, false), (112, true), (114, true), (153, false), (127, false), (141, false), (70, true), (85, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_tail_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, false), (1820, false), (311, false), (95, false), (34, true), (50, true), (69, true), (35, false), (112, true), (114, true), (153, false), (127, false), (141, false), (70, true), (85, false), (87, false), (55, true), (176, false), (101, false), (116, false), (195, false), (56, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_tail_b001_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, false), (1820, false), (311, false), (95, false), (34, false), (54, true), (58, false), (112, true), (114, true), (153, false), (127, false), (141, false), (50, true), (57113, true), (69, true), (70, false), (55, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_tail_b002_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, false), (1820, false), (311, false), (95, false), (34, true), (50, true), (69, true), (35, false), (112, true), (114, true), (153, false), (127, false), (141, false), (70, false), (88, false), (56, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_tail_b003_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, false), (1820, false), (311, false), (95, false), (34, true), (50, true), (69, true), (35, false), (112, true), (114, true), (153, false), (127, false), (141, false), (70, true), (85, false), (87, false), (55, true), (176, false), (101, false), (116, false), (195, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_tail_b004_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, true), (98, false), (44, true), (35, false), (56, true), (34, true), (50, true), (70, true), (85, false), (87, false), (95, false), (113, true), (140, false), (111, false), (114, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_tail_b005_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, false), (1820, false), (311, false), (95, false), (34, false), (54, true), (58, false), (112, true), (114, true), (153, false), (127, false), (141, false), (50, true), (57113, true), (69, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_tail_b006_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, false), (1820, false), (311, false), (95, false), (34, true), (50, true), (69, true), (35, false), (112, true), (114, true), (153, false), (127, false), (141, false), (70, true), (85, false), (87, false), (55, true), (176, false), (101, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_tail_b007_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, false), (1820, false), (311, false), (95, false), (34, false), (54, true), (58, false), (112, true), (114, true), (153, false), (127, false), (141, false), (50, true), (57113, true), (69, true), (70, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_tail_b008_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, false), (1820, false), (311, false), (95, false), (34, true), (50, true), (69, true), (35, false), (112, true), (114, true), (153, false), (127, false), (141, false), (70, true), (85, false), (87, false), (55, true), (176, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_tail_b009_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, false), (1820, false), (311, false), (95, false), (34, true), (50, true), (69, true), (35, false), (112, true), (114, true), (153, false), (127, false), (141, false), (70, true), (85, false), (87, false), (55, true), (176, false), (101, false), (116, false), (195, false), (56, true), (86, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_tail_b010_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, false), (1820, false), (311, false), (95, false), (34, true), (50, true), (69, true), (35, false), (112, true), (114, true), (153, false), (127, false), (141, false), (70, true), (85, false), (87, false), (55, true), (176, false), (101, false), (116, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_tail_b011_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, false), (1820, false), (311, false), (95, false), (34, true), (50, true), (69, true), (35, false), (112, true), (114, true), (153, false), (127, false), (141, false), (70, false), (88, false), (56, true), (87, true), (85, false), (101, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_tail_b012_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, false), (1820, false), (311, false), (95, false), (34, true), (50, true), (69, true), (35, false), (112, true), (114, true), (153, false), (127, false), (141, false), (70, false), (88, false), (56, true), (87, true), (85, false), (101, false), (116, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_tail_b013_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, false), (1820, false), (311, false), (95, false), (34, true), (50, true), (69, true), (35, false), (112, true), (114, true), (153, false), (127, false), (141, false), (70, false), (88, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_tail_b014_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, false), (1820, false), (311, false), (95, false), (34, true), (50, true), (69, true), (35, false), (112, true), (114, true), (153, false), (127, false), (141, false), (70, false), (88, false), (56, true), (87, true), (85, false), (101, false), (116, false), (203, true), (187, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_tail_b015_batch0_unsat [(22, true), (41, false), (64, false), (42, false), (82, true), (98, false), (44, true), (35, false), (56, true), (34, true), (50, true), (70, true), (85, false), (87, false), (95, false), (113, true), (140, false), (111, false), (114, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_requeue_b019_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, false), (1820, false), (311, false), (95, false), (34, true), (50, true), (69, true), (35, false), (112, true), (114, true), (153, false), (127, false), (141, false), (70, false), (88, false), (56, true), (87, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_requeue_b021_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, false), (1820, false), (311, false), (95, false), (34, true), (50, true), (69, true), (35, false), (112, true), (114, true), (153, false), (127, false), (141, false), (70, false), (88, false), (56, true), (87, true), (85, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_requeue_b023_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, false), (1820, false), (311, false), (95, false), (34, true), (50, true), (69, true), (35, false), (112, true), (114, true), (153, false), (127, false), (141, false), (70, true), (85, false), (87, false), (55, true), (176, false), (101, false), (116, false), (195, false), (56, true), (86, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_requeue_b030_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, false), (1820, false), (311, false), (95, false), (34, true), (50, true), (69, true), (35, false), (112, true), (114, true), (153, false), (127, false), (141, false), (70, false), (88, false), (56, true), (87, true), (85, false), (101, false), (116, false), (203, true), (187, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_requeue_b031_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, false), (1820, false), (311, false), (95, false), (34, true), (50, true), (69, true), (35, false), (112, true), (114, true), (153, false), (127, false), (141, false), (70, false), (88, false), (56, true), (87, true), (85, false), (101, false), (116, false), (203, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact d10_requeue_b039_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, false), (1820, false), (311, false), (95, false), (34, false), (54, true), (58, false), (112, true), (114, true), (153, false), (127, false), (141, false), (50, true), (57113, true), (69, true), (70, false), (55, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    exact d10_requeue_b040_batch0_unsat [(22, true), (41, false), (64, true), (111, false), (83, true), (1904, true), (97, false), (1820, false), (311, false), (95, false), (34, true), (50, false), (88, false), (35, false), (49, true), (56, true), (112, true), (114, true), (153, false), (127, false)] (by decide)
    all_goals cases hc
  apply row_excl_of_unsat
  exact BookRamsey.unsat_of_cubes (rcnf 22 4 7 10 7 10)
    cubes_d10 hunit unsat_d10_coverage

end BookRamsey.R47
