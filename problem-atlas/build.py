"""Generate the data-driven pieces of atlas.tex (table, heat map, charts).

Each problem: (name, field, year posed, tier, difficulty D 1-10, fit F 0-5, status).
D and F are the author's (Claude's) subjective judgements, explained in the PDF.
"""
from collections import Counter, defaultdict

FIELDS = {
    "NT": "Number theory", "AN": "Analysis \\& PDE", "AG": "Algebraic geometry",
    "AL": "Algebra \\& groups", "TO": "Topology", "CO": "Combinatorics",
    "GR": "Graph theory", "DG": "Discrete geometry", "AC": "Additive combinatorics",
    "CX": "Complexity", "LO": "Logic \\& computability", "DY": "Dynamics",
    "PH": "Math.\\ physics", "PR": "Probability",
}

P = [
 # ---- Tier Omega: beyond Fields ----
 ("Riemann Hypothesis","NT",1859,"O",10,2,r"$>41\%$ of zeros proved on the line; $10^{13}$ zeros checked"),
 ("P vs NP","CX",1971,"O",10,2,r"Three barriers: relativization, natural proofs, algebrization"),
 ("Navier--Stokes regularity","AN",1934,"O",10,1,r"An averaged NS equation blows up (Tao 2016), so energy methods alone fail"),
 ("Yang--Mills mass gap","PH",1954,"O",10,0,r"No interacting 4D quantum field theory has been rigorously built"),
 ("Hodge conjecture","AG",1950,"O",10,1,r"Known for $(1,1)$-classes (Lefschetz); open in general"),
 ("Birch--Swinnerton-Dyer","NT",1965,"O",10,1,r"Analytic rank $\le1$ (Gross--Zagier, Kolyvagin); positive proportion of curves"),
 ("Langlands functoriality","NT",1967,"O",10,0,r"Geometric Langlands proved (2024, $\sim$1000 pp); arithmetic case wide open"),
 ("Grothendieck's standard conjectures","AG",1968,"O",10,1,r"Special cases only; would give a theory of motives"),
 ("Twin prime conjecture","NT",1849,"O",10,2,r"Gaps $\le246$ infinitely often (Zhang, Maynard, Polymath); parity barrier"),
 ("Goldbach conjecture (strong)","NT",1742,"O",10,2,r"Weak (ternary) Goldbach proved (Helfgott 2013); checked to $4\cdot10^{18}$"),
 # ---- Tier S: Fields-level ----
 ("abc conjecture (accepted proof)","NT",1985,"S",9,2,r"IUT claim (Mochizuki 2012) disputed by Scholze--Stix (2018)"),
 ("Collatz conjecture","NT",1937,"S",9,2,r"Almost all orbits attain almost bounded values (Tao 2019)"),
 ("Frege lower bounds (Frege vs EF)","CX",1979,"S",9,3,r"No superpolynomial Frege lower bound; tied to our naming project"),
 ("Explicit circuit lower bounds","CX",1949,"S",9,3,r"Best $\approx3.1n$ for circuits, $\approx n^3$ for formulas"),
 ("VP vs VNP","CX",1979,"S",9,2,r"Permanent needs determinants of size $\ge n^2/2$ (Mignon--Ressayre)"),
 ("Unique Games Conjecture","CX",2002,"S",8,3,r"2-to-2 Games Theorem (Khot--Minzer--Safra 2018)"),
 (r"Matrix multiplication $\omega=2$","CX",1969,"S",9,2,r"$\omega<2.3714$; barriers for laser-method variants"),
 ("Smooth 4D Poincar\\'e conjecture","TO",1982,"S",9,1,r"Topological case: Freedman (1982); smooth case open"),
 (r"Kakeya conjecture, $n\ge4$","AN",1971,"S",8,3,r"Solved in $\mathbb R^3$ (Wang--Zahl 2025)"),
 ("Fourier restriction conjecture","AN",1967,"S",9,2,r"Polynomial partitioning and decoupling give partial ranges"),
 ("Jacobian conjecture","AL",1939,"S",9,3,r"Reduced to cubic homogeneous maps; many false proofs"),
 ("Inverse Galois problem","AL",1892,"S",9,1,r"All solvable groups (Shafarevich); $M_{23}$ the only open sporadic"),
 ("Hilbert's 12th problem","NT",1900,"S",9,1,r"Totally real fields: Dasgupta--Kakde (2021+)"),
 ("Lindel\\\"of hypothesis","NT",1908,"S",9,2,r"$\zeta(\tfrac12+it)\ll t^{13/84+\varepsilon}$ (Bourgain 2017)"),
 ("Elliott--Halberstam conjecture","NT",1968,"S",9,2,r"Level $1/2$ (Bombieri--Vinogradov); beyond for smooth moduli"),
 ("Chowla and Sarnak conjectures","NT",1965,"S",9,2,r"Log-averaged two-point Chowla (Tao 2016)"),
 ("Hadwiger's conjecture","GR",1943,"S",9,3,r"True for $t\le6$; $O(t\log\log t)$ colours (Delcourt--Postle)"),
 ("Erd\\H{o}s--Hajnal conjecture","GR",1989,"S",8,4,r"$P_5$-free case proved (Nguyen--Scott--Seymour 2023)"),
 ("Tate conjecture","AG",1963,"S",9,1,r"Divisors on abelian varieties (Faltings); K3 surfaces"),
 (r"Resolution of singularities, char $p$","AG",1964,"S",9,1,r"Known up to dimension 3"),
 ("Novikov / Baum--Connes","TO",1965,"S",9,1,r"Hyperbolic and amenable groups; groupoid counterexamples"),
 ("Invariant subspace problem","AN",1935,"S",8,3,r"False on some Banach spaces (Enflo, Read); Hilbert space open"),
 ("3D Euler: smooth blow-up?","AN",1757,"S",9,1,r"Blow-up with a boundary (Chen--Hou 2022, computer-assisted)"),
 ("Hilbert's 16th (limit cycles)","DY",1900,"S",9,1,r"No uniform bound even for quadratic vector fields"),
 ("Sunflower conjecture","CO",1960,"S",8,4,r"$(C\log k)^k$-type bounds via spread sets (ALWZ 2019, Rao)"),
 ("MLC: Mandelbrot set locally connected","DY",1985,"S",9,1,r"Known at many parameters (Yoccoz); open in general"),
 ("Diagonal Ramsey growth rate","CO",1947,"S",9,3,r"$R(k)\le(4-\varepsilon)^k$ (Campos--Griffiths--Morris--Sahasrabudhe 2023)"),
 (r"Hilbert's 10th problem over $\mathbb Q$","LO",1970,"S",9,2,r"Undecidable over all rings of integers (Koymans--Pagano 2024)"),
 ("Quantum PCP conjecture","CX",2006,"S",9,3,r"NLTS theorem (Anshu--Breuckmann--Nirkhe 2022)"),
 # ---- Tier A: major breakthrough ----
 ("Erd\\H{o}s arithmetic-progression conj.","AC",1936,"A",8,3,r"$k=3$ proved (Bloom--Sisask 2020); Erd\H{o}s offered \$5000"),
 ("Union-closed sets (Frankl)","CO",1979,"A",7,5,r"Constant $\approx0.38$ (Gilmer 2022 and successors); $1/2$ open"),
 ("Chromatic number of the plane","DG",1950,"A",8,2,r"$5\le\chi\le7$ (de Grey 2018, computer-assisted)"),
 ("Lonely runner conjecture","NT",1967,"A",7,3,r"Proved for up to 7 runners; recent computer-assisted extensions"),
 ("Odd perfect numbers","NT",-300,"A",8,1,r"Any example exceeds $10^{1500}$ (Ochem--Rao)"),
 (r"Primes of the form $n^2+1$","NT",1912,"A",9,1,r"$n^2+1$ has $\le2$ prime factors infinitely often (Iwaniec)"),
 (r"Legendre: prime in $(n^2,(n+1)^2)$","NT",1808,"A",9,1,r"Not implied even by RH; gaps $x^{0.525}$ (Baker--Harman--Pintz)"),
 (r"Irrationality of $e+\pi$, $e\pi$, $\gamma$","NT",1900,"A",9,2,r"At least one of $e+\pi$, $e\pi$ is transcendental"),
 (r"Irrationality of $\zeta(5)$","NT",1979,"A",8,3,r"One of $\zeta(5),\zeta(7),\zeta(9),\zeta(11)$ irrational (Zudilin 2001)"),
 ("Schanuel's conjecture","NT",1966,"A",9,1,r"Would give algebraic independence of $e$ and $\pi$"),
 ("Littlewood conjecture","NT",1930,"A",8,2,r"Exceptions have dimension 0 (Einsiedler--Katok--Lindenstrauss)"),
 ("Lehmer's Mahler-measure problem","NT",1933,"A",8,3,r"Lehmer's $1.17628\ldots$ still the smallest known value"),
 ("Artin's primitive-root conjecture","NT",1927,"A",9,1,r"True under GRH (Hooley 1967)"),
 ("Gauss circle / Dirichlet divisor","NT",1849,"A",8,2,r"Exponent $\approx0.3145$ vs.\ conjectured $1/4$"),
 ("\\v{C}ern\\'y conjecture","CO",1964,"A",7,5,r"Best bound $\approx n^3/6$; conjecture $(n-1)^2$"),
 ("Graceful tree conjecture","GR",1964,"A",7,4,r"Ringel's conjecture proved (Montgomery--Pokrovskiy--Sudakov 2020)"),
 ("Graph reconstruction conjecture","GR",1942,"A",8,3,r"Checked to 13 vertices; true for almost all graphs"),
 ("Cycle double cover conjecture","GR",1973,"A",8,4,r"Reduced to snarks"),
 ("Tutte's 5-flow conjecture","GR",1954,"A",8,4,r"Every bridgeless graph has a 6-flow (Seymour 1981)"),
 ("List colouring conjecture","GR",1975,"A",8,3,r"Bipartite case (Galvin 1995); asymptotically (Kahn 1996)"),
 ("Erd\\H{o}s unit-distance problem","DG",1946,"A",8,3,r"Upper bound $O(n^{4/3})$ unchanged since 1984"),
 ("Heilbronn triangle problem","DG",1950,"A",7,4,r"$n^{-8/7-1/2000}$ (Cohen--Pohoata--Zakharov 2023)"),
 ("Mahler volume conjecture","DG",1939,"A",8,3,r"Proved in dimension 3 (Iriyeh--Shibata 2020)"),
 ("Hot spots conjecture","AN",1974,"A",7,3,r"Proved for triangles (Judge--Mondal 2022)"),
 ("Hadamard conjecture","CO",1893,"A",8,2,r"Smallest unknown order: 668"),
 (r"Exact value of $R(5,5)$","CO",1955,"A",8,1,r"$43\le R(5,5)\le46$ (Angeltveit--McKay 2024)"),
 ("Andrews--Curtis conjecture","TO",1965,"A",8,3,r"Widely believed false; candidate counterexamples remain"),
 ("Whitehead asphericity conjecture","TO",1941,"A",8,3,r"Open for over 80 years"),
 ("Kaplansky zero-divisor conjecture","AL",1956,"A",8,3,r"Unit conjecture disproved (Gardam 2021)"),
 (r"Polynomial Freiman--Ruzsa over $\mathbb Z$","AC",1999,"A",8,4,r"Proved over $\mathbb F_2^n$ (Gowers--Green--Manners--Tao 2023)"),
 ("Sum--product conjecture","AC",1983,"A",8,4,r"Exponent $4/3+c$ (Rudnev--Stevens 2020)"),
 ("Log-rank conjecture","CX",1988,"A",8,4,r"$O(\sqrt{\mathrm{rank}})$ (Lovett; Sudakov--Tomon)"),
 ("Polynomial Hirsch conjecture","DG",1957,"A",8,4,r"Hirsch disproved (Santos 2010); quasi-polynomial bound"),
 ("Graph isomorphism in P","CX",1972,"A",8,3,r"Quasipolynomial time (Babai 2015)"),
 (r"Furstenberg $\times2\times3$ conjecture","DY",1967,"A",9,2,r"Positive-entropy case (Rudolph 1990)"),
 ("Zauner's conjecture (SIC-POVMs)","PH",1999,"A",8,3,r"Exact solutions in many dimensions; tied to Hilbert's 12th"),
 (r"3D percolation at $p_c$","PR",1957,"A",9,2,r"Known in 2D and for $d\ge11$"),
 (r"Burnside: is $B(2,5)$ finite?","AL",1902,"A",8,2,r"Exponents 2,3,4,6 finite; large odd exponents infinite"),
 ("Vaught's conjecture","LO",1961,"A",8,3,r"Counterexamples ruled out in many classes"),
 # ---- Tier B: strong research problems ----
 ("Rota's basis conjecture","CO",1989,"B",7,4,r"$n-o(n)$ disjoint transversal bases (Pokrovskiy 2020)"),
 ("Ryser's conjecture (Latin transversals)","CO",1967,"B",7,4,r"Partial transversal of size $n-1$, large $n$ (Montgomery 2023)"),
 ("Seymour's second-neighbourhood conj.","GR",1990,"B",6,5,r"Known for tournaments (Fisher 1996)"),
 ("Caccetta--H\\\"aggkvist conjecture","GR",1978,"B",7,4,r"Even the triangle case is open"),
 ("Erd\\H{o}s--Gy\\'arf\\'as conjecture","GR",1995,"B",6,5,r"Known for claw-free graphs and some planar classes"),
 ("Lov\\'asz path conjecture","GR",1969,"B",7,3,r"Only 5 non-Hamiltonian vertex-transitive graphs known"),
 ("Erd\\H{o}s--Tur\\'an additive bases","AC",1941,"B",8,3,r"Erd\H{o}s offered \$500"),
 ("Happy ending problem (exact)","DG",1935,"B",7,3,r"$2^{n+o(n)}$ (Suk 2017); exact $2^{n-2}+1$ open"),
 ("Conway's 99-graph problem","GR",1975,"B",6,3,r"Conway offered \$1000"),
 ("Moore graph of degree 57","GR",1960,"B",7,3,r"Would have 3250 vertices; cannot be vertex-transitive"),
 ("Projective plane of order 12","CO",1938,"B",8,1,r"Order 10 ruled out by computer (Lam 1989)"),
 ("Singmaster's conjecture","NT",1971,"B",6,3,r"No number known to appear $>8$ times in Pascal's triangle"),
 (r"Brocard's problem $n!+1=m^2$","NT",1876,"B",8,2,r"Finitely many solutions if abc holds (Overholt)"),
 ("Perfect cuboid","NT",1719,"B",7,2,r"Euler bricks exist; no perfect one known"),
 ("Lehmer's totient problem","NT",1932,"B",7,2,r"A counterexample needs many prime factors"),
 ("1/3--2/3 conjecture (posets)","CO",1968,"B",7,5,r"$\delta\ge0.276$ (Brightwell--Felsner--Trotter 1995)"),
 ("Gy\\'arf\\'as--Sumner conjecture","GR",1975,"B",8,4,r"Known for paths, stars and some trees"),
 ("Odd covering systems","NT",1952,"B",7,4,r"Minimum-modulus problem solved (Hough 2015)"),
 (r"Sidon sets: $\sqrt n+O(1)$?","AC",1941,"B",7,4,r"$\sqrt n+0.998\,n^{1/4}$ (Balogh--F\"uredi--Roy 2023)"),
 ("Toeplitz inscribed square","DG",1911,"B",7,4,r"Smooth curves done; rectangles (Greene--Lobb 2020)"),
 ("Sendov's conjecture (all degrees)","AN",1958,"B",6,4,r"True for large degree (Tao 2020)"),
 (r"Busy Beaver $BB(6)$","LO",1962,"B",8,0,r"$BB(5)=47{,}176{,}870$ (2024, in Coq); $BB(6)$ hides Collatz-like machines"),
]
assert len(P) == 100, len(P)

TCOL = {"O": "tO", "S": "tS", "A": "tA", "B": "tB"}

def table():
    out, last = [], None
    heads = {"O": r"Tier $\Omega$ --- beyond Fields (would reshape mathematics)",
             "S": r"Tier S --- Fields-level (a solution is a career-defining, prize-certain result)",
             "A": r"Tier A --- major breakthrough (top-journal paper, major prize)",
             "B": r"Tier B --- strong research problem (excellent paper, notable)"}
    for i, (n, f, y, t, d, fit, s) in enumerate(P, 1):
        if t != last:
            out.append(r"\multicolumn{6}{l}{\cellcolor{%s}\color{white}\bfseries\rule{0pt}{2.6ex}%s}\\" % (TCOL[t], heads[t]))
            last = t
        yr = ("c.\\,300 BC" if y < 0 else str(y))
        row = r"\rowcolor{%s!%d}" % (TCOL[t], 6 if i % 2 else 13)
        out.append(row + r"\textbf{%d} & \textbf{%s}\newline{\color{black!60}\scriptsize %s} & %s & %s & \D{%d} & \F{%d}\\"
                   % (i, n, FIELDS[f], yr, s, d, fit))
    return "\n".join(out)

def heatmap():
    cells = defaultdict(list)
    for i, (n, f, y, t, d, fit, s) in enumerate(P, 1):
        cells[(d, fit)].append((i, t))
    W, H = 2.55, 1.55
    o = []
    for d in range(6, 11):
        for fit in range(0, 6):
            items = cells[(d, fit)]
            x, yy = (d - 6) * W, fit * H
            shade = min(10 + 9 * len(items), 75) if items else 0
            sweet = (fit >= 4 and d <= 8)
            fill = ("tG!%d" % min(12 + 4 * len(items), 32)) if sweet else ("black!%d" % (shade // 3))
            o.append(r"\fill[%s,rounded corners=3pt] (%.2f,%.2f) rectangle ++(%.2f,%.2f);" % (fill, x + .04, yy + .04, W - .08, H - .08))
            if items:
                txt = " ".join(r"\textcolor{%s}{\textbf{%d}}" % (TCOL[t], i) for i, t in items)
                o.append(r"\node[text width=%.2fcm,align=center,font=\scriptsize] at (%.2f,%.2f) {%s};" % (W - .25, x + W / 2, yy + H / 2, txt))
    for d in range(6, 11):
        o.append(r"\node[font=\small\bfseries] at (%.2f,-0.35) {%d};" % ((d - 6) * W + W / 2, d))
    for fit in range(0, 6):
        o.append(r"\node[font=\small\bfseries,anchor=east] at (-0.1,%.2f) {%d};" % (fit * H + H / 2, fit))
    o.append(r"\draw[tG,line width=2pt,rounded corners=5pt,dashed] (0,%.2f) rectangle (%.2f,%.2f);" % (4 * H, 3 * W, 6 * H))
    o.append(r"\node[tG!70!black,font=\bfseries\small,fill=white,rounded corners=2pt] at (%.2f,%.2f) {sweet spot};" % (1.5 * W, 6 * H + .05))
    o.append(r"\node[font=\small] at (%.2f,-0.95) {Difficulty $D$ (how far current methods are from a solution) $\longrightarrow$};" % (2.5 * W))
    o.append(r"\node[font=\small,rotate=90] at (-0.75,%.2f) {Raw-reasoning fit $F$ $\longrightarrow$};" % (3 * H))
    return "\n".join(o)

def fields():
    cnt = defaultdict(Counter)
    for n, f, y, t, d, fit, s in P:
        cnt[f][t] += 1
    order = sorted(cnt, key=lambda f: (sum(cnt[f].values()), f))
    labels = ",".join("{%s}" % FIELDS[f] for f in order)
    plots = []
    for t in "OSAB":
        coords = " ".join("(%d,%d)" % (cnt[f][t], k) for k, f in enumerate(order))
        plots.append(r"\addplot[fill=%s,draw=white] coordinates {%s};" % (TCOL[t], coords))
    return labels, "\n".join(plots), len(order)

def age():
    rows = []
    for i, (n, f, y, t, d, fit, s) in enumerate(P, 1):
        rows.append("%d %.2f %s" % (2026 - y, d + ((i * 37) % 11 - 5) * 0.045, t))
    return "x y t\n" + "\n".join(rows)

def stats():
    by = defaultdict(list)
    for n, f, y, t, d, fit, s in P:
        by[t].append(fit)
    return {t: sum(v) / len(v) for t, v in by.items()}

if __name__ == "__main__":
    frame = open("table_frame.tex").read()
    open("gen_table.tex", "w").write(frame.replace("%%ROWS%%", table()))
    open("gen_heatmap.tex", "w").write(heatmap())
    labels, plots, nf = fields()
    open("gen_fields.tex", "w").write(
        "\\def\\fieldlabels{%s}\n\\def\\nfields{%d}\n\\def\\fieldplots{%s}\n" % (labels, nf - 1, plots))
    for t in "OSAB":
        rows = [r for r in age().splitlines()[1:] if r.endswith(" " + t)]
        open("gen_age_%s.dat" % t, "w").write("x y t\n" + "\n".join(rows) + "\n")
    s = stats()
    open("gen_stats.tex", "w").write("".join(
        "\\def\\avgfit%s{%.1f}\n" % ({"O": "O", "S": "S", "A": "A", "B": "B"}[t], v) for t, v in s.items()))
    print({t: round(v, 2) for t, v in s.items()}, Counter(p[3] for p in P))
