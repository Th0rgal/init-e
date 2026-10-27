import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Pass767_4
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def word767_5_1496 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1
  [(2, 6981), (4, 6985), (6, 6989), (8, 6993), (10, 6997), (12, 7001), (14, 6981), (16, 6985), (18, 6989), (20, 6993),
    (22, 6997), (24, 7001)]

def word767_5_1530 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1496 word767_3_1529

def word767_5_1531 : WordLangProgHOL (BitVec 64) :=
.seq word767_2_1794 word767_5_1530

def word767_5_1532 : WordLangProgHOL (BitVec 64) :=
.seq word767_3_1494 word767_5_1531

def word767_5_1533 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1532 word767_0_27

def word767_5_1535 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1533 word767_2_1842

def word767_5_1537 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1535 word767_2_1844

def word767_5_1539 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1537 word767_2_1846

def word767_5_1541 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1539 word767_2_1848

def word767_5_1543 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1541 word767_2_1850

def word767_5_1545 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1543 word767_2_1852

def word767_5_1547 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1545 word767_2_1854

def word767_5_1549 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1547 word767_2_1856

def word767_5_1551 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1549 word767_2_1858

def word767_5_1553 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1551 word767_2_1860

def word767_5_1555 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1553 word767_2_1862

def word767_5_1557 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1555 word767_2_1864

def word767_5_1595 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1557 word767_3_1594

def word767_5_1596 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1595 word767_0_27

def word767_5_1598 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1596 word767_2_1914

def word767_5_1600 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1598 word767_2_1916

def word767_5_1602 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1600 word767_2_1918

def word767_5_1604 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1602 word767_2_1920

def word767_5_1606 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1604 word767_2_1922

def word767_5_1608 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1606 word767_2_1924

def word767_5_1610 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1608 word767_2_1926

def word767_5_1612 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1610 word767_2_1928

def word767_5_1614 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1612 word767_2_1930

def word767_5_1616 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1614 word767_2_1932

def word767_5_1618 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1616 word767_2_1934

def word767_5_1620 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1618 word767_2_1936

def word767_5_1658 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1620 word767_3_1657

def word767_5_1659 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1658 word767_0_27

def word767_5_1661 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1659 word767_2_1986

def word767_5_1663 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1661 word767_2_1988

def word767_5_1665 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1663 word767_2_1990

def word767_5_1667 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1665 word767_2_1992

def word767_5_1669 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1667 word767_2_1994

def word767_5_1671 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1669 word767_2_1996

def word767_5_1673 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1671 word767_2_1998

def word767_5_1675 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1673 word767_2_2000

def word767_5_1677 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1675 word767_2_2002

def word767_5_1679 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1677 word767_2_2004

def word767_5_1681 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1679 word767_2_2006

def word767_5_1683 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1681 word767_2_2008

def word767_5_1721 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1683 word767_3_1720

def word767_5_1722 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1721 word767_0_27

def word767_5_1724 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1722 word767_2_2058

def word767_5_1726 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1724 word767_2_2060

def word767_5_1728 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1726 word767_2_2062

def word767_5_1730 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1728 word767_2_2064

def word767_5_1732 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1730 word767_2_2066

def word767_5_1734 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1732 word767_2_2068

def word767_5_1736 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1734 word767_2_2070

def word767_5_1738 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1736 word767_2_2072

def word767_5_1740 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1738 word767_2_2074

def word767_5_1742 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1740 word767_2_2076

def word767_5_1744 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1742 word767_2_2078

def word767_5_1746 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1744 word767_2_2080

def word767_5_1784 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1746 word767_3_1783

def word767_5_1785 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1784 word767_0_27

def word767_5_1787 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1785 word767_2_2130

def word767_5_1789 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1787 word767_2_2132

def word767_5_1791 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1789 word767_2_2134

def word767_5_1793 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1791 word767_2_2136

def word767_5_1795 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1793 word767_2_2138

def word767_5_1797 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1795 word767_2_2140

def word767_5_1799 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1797 word767_2_2142

def word767_5_1801 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1799 word767_2_2144

def word767_5_1803 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1801 word767_2_2146

def word767_5_1805 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1803 word767_2_2148

def word767_5_1807 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1805 word767_2_2150

def word767_5_1809 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1807 word767_2_2152

def word767_5_1847 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1809 word767_3_1846

def word767_5_1848 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1847 word767_0_27

def word767_5_1850 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1848 word767_2_2202

def word767_5_1852 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1850 word767_2_2204

def word767_5_1854 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1852 word767_2_2206

def word767_5_1856 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1854 word767_2_2208

def word767_5_1858 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1856 word767_2_2210

def word767_5_1860 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1858 word767_2_2212

def word767_5_1862 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1860 word767_2_2214

def word767_5_1864 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1862 word767_2_2216

def word767_5_1866 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1864 word767_2_2218

def word767_5_1868 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1866 word767_2_2220

def word767_5_1870 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1868 word767_2_2222

def word767_5_1872 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1870 word767_2_2224

def word767_5_1910 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1872 word767_3_1909

def word767_5_1911 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1910 word767_0_27

def word767_5_1913 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1911 word767_2_2274

def word767_5_1915 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1913 word767_2_2276

def word767_5_1917 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1915 word767_2_2278

def word767_5_1919 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1917 word767_2_2280

def word767_5_1921 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1919 word767_2_2282

def word767_5_1923 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1921 word767_2_2284

def word767_5_1925 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1923 word767_2_2286

def word767_5_1927 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1925 word767_2_2288

def word767_5_1929 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1927 word767_2_2290

def word767_5_1931 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1929 word767_2_2292

def word767_5_1933 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1931 word767_2_2294

def word767_5_1935 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1933 word767_2_2296

def word767_5_1973 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1935 word767_3_1972

def word767_5_1974 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1973 word767_0_27

def word767_5_1976 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1974 word767_2_2346

def word767_5_1978 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1976 word767_2_2348

def word767_5_1980 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1978 word767_2_2350

def word767_5_1982 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1980 word767_2_2352

def word767_5_1984 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1982 word767_2_2354

def word767_5_1986 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1984 word767_2_2356

def word767_5_1988 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1986 word767_2_2358

def word767_5_1990 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1988 word767_2_2360

def word767_5_1994 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1990 word767_2_2364

def word767_5_1996 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1994 word767_2_2366

def word767_5_2000 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_1996 word767_2_2370

def word767_5_2002 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_2000 word767_2_2372

def word767_5_2006 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_2002 word767_2_2376

def word767_5_2008 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_2006 word767_2_2378

def word767_5_2012 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_2008 word767_2_2382

def word767_5_2014 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_2012 word767_2_2384

def word767_5_2018 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_2014 word767_2_2388

def word767_5_2020 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_2018 word767_2_2390

def word767_5_2024 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_2020 word767_2_2394

def word767_5_2025 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(9801, 9797)]

def word767_5_2027 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_2025 word767_2_2397

def word767_5_2028 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_2024 word767_5_2027

def word767_5_2030 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_2028 word767_2_2400

def word767_5_2032 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_2030 word767_2_2402

def word767_5_2034 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_2032 word767_2_2404

def word767_5_2036 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_2034 word767_2_2406

def word767_5_2038 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_2036 word767_2_2408

def word767_5_2040 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_2038 word767_2_2410

def word767_5_2042 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_2040 word767_2_2412

def word767_5_2046 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_2042 word767_2_2416

def word767_5_2048 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_2046 word767_2_2418

def word767_5_2052 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_2048 word767_2_2422

def word767_5_2054 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_2052 word767_2_2424

def word767_5_2058 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_2054 word767_2_2428

def word767_5_2060 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_2058 word767_2_2430

def word767_5_2064 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_2060 word767_2_2434

def word767_5_2066 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_2064 word767_2_2436

def word767_5_2070 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_2066 word767_2_2440

def word767_5_2072 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_2070 word767_2_2442

def word767_5_2076 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_2072 word767_2_2446

def word767_5_2080 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_2076 word767_2_2450

def word767_5_2082 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_2080 word767_2_2452

def word767_5_2084 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_2082 word767_2_2454

def word767_5_2086 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_2084 word767_2_2456

def word767_5_2088 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_2086 word767_2_2458

def word767_5_2090 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_2088 word767_2_2460

def word767_5_2092 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_2090 word767_2_2462

def word767_5_2094 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_2092 word767_2_2464

def word767_5_2098 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_2094 word767_2_2468

def word767_5_2100 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_2098 word767_2_2470

def word767_5_2104 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_2100 word767_2_2474

def word767_5_2106 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_2104 word767_2_2476

def word767_5_2110 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_2106 word767_2_2480

def word767_5_2112 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_2110 word767_2_2482

def word767_5_2116 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_2112 word767_2_2486

def word767_5_2118 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_2116 word767_2_2488

def word767_5_2122 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_2118 word767_2_2492

def word767_5_2124 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_2122 word767_2_2494

def word767_5_2128 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_2124 word767_2_2498

def word767_5_2130 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_2128 word767_2_2500

def word767_5_2134 : WordLangProgHOL (BitVec 64) :=
.seq word767_5_2130 word767_2_2504

def word767_5_2135 : WordLangProgHOL (BitVec 64) :=
.seq word767_2_0 word767_5_2134

def pass767_5 : WordLangProgHOL (BitVec 64) :=
word767_5_2135
theorem pass767_5_eq : WordCopy.copyProp (pass767_4) = pass767_5 := by
  kernel_rfl
#print axioms pass767_5_eq
end InitECandidate.Proofs.WordStages
