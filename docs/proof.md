# The Quarter Lemma, and the exact ρ-partitions are not permutable (Erdős #197, partial result)

*Partial progress on [Erdős Problem #197](https://www.erdosproblems.com/197). The problem itself remains open, and this note does not solve it.*

## Background

**Problem (Erdős–Graham).** Can $\mathbb N$ be partitioned into two sets, each of which admits an enumeration (a listing of order type $\omega$) with no monotone 3-term arithmetic progression? Call $S\subseteq\mathbb N$ *permutable* if it has such an enumeration.

Davis, Entringer, Graham and Simmons (1977) showed that $\mathbb N$ itself is not permutable. W. Kasel (arXiv:2609.02939, 2026) showed that the dyadic partition fails, with a finite *order gadget* and a toolkit of ladder lemmas (zigzag and flood, his Lemmas 23–26). Two earlier repositories of this project formalize consequences of that toolkit: Theorem I ([Alex-lop/erdos-197-interval-gadget](https://github.com/Alex-lop/erdos-197-interval-gadget)) and the tower obstruction Theorem R\* ([Alex-lop/erdos-197-tower-obstruction](https://github.com/Alex-lop/erdos-197-tower-obstruction)), which kills every alternating run colouring whose run ratios tend to $2$. Colourings with *short* runs (ratio below $7/4$) are out of reach of R\*.

The simplest such colourings are the **exact ρ-partitions**: for $k\ge1$ and a real phase $\varphi$, colour $n\ge1$ by the parity of $\lfloor(2k+1)(\log_2 n-\varphi)\rfloor$. Every octave $[x,2x)$ then consists of $K=2k+1$ runs of ratio $2^{1/K}\le2^{1/3}$, of alternating colours. This note proves:

* **Quarter Lemma** (Section 3). In an admissible order of an interval $[\alpha,\beta]$, $\beta-\alpha\ge8$, every point of the *leading quarter* precedes every point of the *trailing parity*, away from the ends (margin $4$).
* **Theorem L\*** for one anchor pair (Section 5). Doubling links between intervals, $2W-\{e,e+1\}\subseteq$ the next interval, form an infinite descending chain of positions; so a set with an infinite chain of such links is not permutable.
* **Theorem 5.2** (Section 7). For every $k\ge1$ and every $\varphi$, **neither** colour class of the exact ρ-partition is permutable. There is no hypothesis on the enumeration (no lag assumption).

Everything in Sections 2–7 is formalized in Lean 4 in this repository (Section 9).

This note is a rewrite of the refereed text, Sections 0–2, 3 (Lemma 3.1), 4 (Theorem 4.1) and 5 (Lemma 5.1, Theorem 5.2) of the project's working note `work/p197_m2_r3/rho/proof.md` (not included in this repository; Section 10 has its history). The following parts are not in the refereed text, so they were not refereed:

* the proof of the Quarter Lemma by **three** cases (Section 3). The refereed proof first reflects the interval so that $q\le(\alpha+\beta)/2$ and then has two cases; here the far side is handled directly (Case 3), so no reflection is needed. The bound $c\le(\beta+q)/2\le\beta-2$ in Case 2 is the simplification suggested by the proof referee;
* Step 0 of the Quarter Lemma (Section 3), which derives "$q$ has the leading parity" from $q\equiv Q\pmod 4$ in the form in which $\pi$ and $Q$ are given here, and the written-out existence of the phases (Lemma 2.1);
* the form of Theorem L\* (Section 5): the refereed Theorem 4.1 allows a finite family of odd-distance anchor pairs and arbitrary 4-windows; here one consecutive pair $e,e+1$ and the bottom windows $[a_m+4,a_m+7]$, which is the case used for Theorem 5.2. The proof is the refereed one;
* the integer form of the B-link (Lemma 6.1) and the proof of Lemma 7.1(iii),(iv) in the detail given here.

Each of these parts is mirrored by the kernel-checked Lean proof (`quarter_good`, `quarter_thm`, `phases`, `link`, `chain`, `blink`, `rho_runs`).

## 0. Setting and conventions

* $S\subseteq\mathbb N$. Integer intervals are $[p,q]=\{p,p+1,\dots,q\}$. The *4-interior* of $[p,q]$ is $[p+4,q-4]$.
* A *3-AP* of $S$ is a triple $x<y<z$ in $S$ with $x+z=2y$.
* A linear order $\prec$ of $S$ is *admissible* if no 3-AP $x<y<z$ of $S$ satisfies $x\prec y\prec z$ or $z\prec y\prec x$. Equivalently (**midpoint rule**): for every 3-AP $x<y<z$ of $S$, $y\prec x\iff y\prec z$. The restriction of an admissible order to a subset is admissible.
* An order has *type $\omega$* if every element has finitely many predecessors. Then $\operatorname{pos}(v)=\#\{s\in S:\ s\prec v\}\in\mathbb N$ is injective and $s\prec s'\iff\operatorname{pos}(s)<\operatorname{pos}(s')$.
* $S$ is *permutable* if it has an admissible order of type $\omega$. For infinite $S$ this is exactly the condition of Erdős #197 and of formal-conjectures (`ErdosProblems/197.lean`): a bijection $f:\mathbb N\simeq S$ with $\neg\,\mathrm{HasMonotoneAP}(\mathrm{Subtype.val}\circ f)\ 3$, and then $\operatorname{pos}=f^{-1}$.

## 1. Ladder tools

Let $\prec$ be an admissible order of an interval $I=[L,R]$. The following are Lemma 1 (zigzag), Lemma 2 (flood) and Rules A, B of the proof of Theorem I ([erdos-197-interval-gadget, `docs/proof.md`](https://github.com/Alex-lop/erdos-197-interval-gadget/blob/main/docs/proof.md), Sections 1–2; Kasel, Lemmas 23–26). Their Lean proofs are in `Erdos197Interval/Basic.lean`, included verbatim.

* **Zigzag** (`Good.alt`). Let $g\ge1$ and $w\le w'$ with $w'-w\in2g\mathbb Z$ and $w,w'+g\in I$. Then $w'\prec w'+g\iff w\prec w+g$. (Induction on $(w'-w)/2g$, using the midpoint rule at $(a,a+g,a+2g)$ and $(a+g,a+2g,a+3g)$.) In particular (`Good.par`, `Good.lead_iff`) points of the same parity have the same orientation towards their right neighbour.
* **Rule A** (`Good.ruleA`). If $w-x$ is odd and $w,2x-w\in I$, then $x\prec w\iff x\prec x+1$.
* **Rule B** (`Good.ruleB`). If $w-x\equiv2\pmod 4$ and $w,2x-w\in I$, then $x\prec w\iff x\prec x+2$.

## 2. Phases

**Lemma 2.1 (phases).** Let $\prec$ be an admissible order of $[\alpha,\beta]$ with $\beta\ge\alpha+8$. There are $\pi\in\{0,1\}$ and $Q$ such that

* (P) for $x\in[\alpha,\beta-1]$: $x\prec x+1\iff x\equiv\pi\pmod 2$;
* (Q) for $x\in[\alpha,\beta-2]$ with $x\equiv\pi$: $x\prec x+2\iff x\equiv Q\pmod 4$.

$\pi$ is the *leading parity* and the points $x\equiv Q\pmod4$ form the *leading quarter*.

*Proof.* By zigzag with $g=1$, $x\prec x+1\iff(\alpha\prec\alpha+1\iff x\equiv\alpha\pmod 2)$; take $\pi\equiv\alpha$ if $\alpha\prec\alpha+1$ and $\pi\equiv\alpha+1$ otherwise. Let $p\in\{\alpha,\alpha+1\}$ with $p\equiv\pi$, and put $Q=p\bmod4$ if $p\prec p+2$, $Q=(p+2)\bmod4$ otherwise. Let $x\equiv\pi$, $x\in[\alpha,\beta-2]$; then $x\ge p$. If $x\equiv p\pmod 4$, zigzag with $g=2$ between the rungs $(p,p+2)$ and $(x,x+2)$ gives $x\prec x+2\iff p\prec p+2$. If $x\equiv p+2\pmod4$, then $x\ge p+2$, and zigzag between $(p+2,p+4)$ and $(x,x+2)$ gives $x\prec x+2\iff p+2\prec p+4$, which by the midpoint rule at $(p,p+2,p+4)$ is equivalent to $p+2\prec p$, i.e. to $\neg(p\prec p+2)$. In both cases $x\prec x+2\iff x\equiv Q\pmod4$. $\square$

## 3. The Quarter Lemma

**Lemma 3.1 (Quarter Lemma).** Let $\prec$ be an admissible order of $[\alpha,\beta]$ with $\beta\ge\alpha+8$, and let $\pi,Q$ satisfy (P) and (Q). Then
$$q\prec z\qquad\text{for all }q,z\in[\alpha+4,\beta-4]\text{ with }q\equiv Q\pmod4,\ z\not\equiv\pi\pmod2.$$

*Proof.* **Step 0: $q\equiv\pi$.** Suppose not. If $q+1\equiv\pi$, then $q-1$ and $q+1$ are $\equiv\pi$ and, as $q\equiv Q\pmod 4$, neither is $\equiv Q\pmod4$; by (Q), $q+1\prec q-1$ and $q+3\prec q+1$, a monotone 3-AP $(q-1,q+1,q+3)$. If $q+1\not\equiv\pi$ as well, then by (P) $q+1\prec q$ and $q+2\prec q+1$, a monotone 3-AP $(q,q+1,q+2)$. So $q\equiv\pi$, and by (P), (Q): $q\prec q+1$ and $q\prec q+2$. By (P), $z+1\prec z$.

It remains to prove the **local form**: *if $q,z\in[\alpha+4,\beta-4]$, $q\prec q+1$, $q\prec q+2$ and $z+1\prec z$, then $q\prec z$.* First, $z-q$ is odd: otherwise zigzag ($g=1$) gives $z\prec z+1\iff q\prec q+1$, so $z\prec z+1$.

*Key step.* Suppose $c\equiv q+2\pmod 4$ satisfies $\alpha+2\le c\le\beta-2$, $2c-q\in[\alpha,\beta]$, $2c-z\in[\alpha,\beta]$, and $c$ *2-trails*: $c+2\prec c$. Then $q\prec z$. Indeed $c\equiv q\pmod2$, so $c\prec c+1$ by zigzag. Rule B at $x=c$, $w=q$ (here $q-c\equiv2\pmod 4$) gives $c\prec q\iff c\prec c+2$, which is false; so $q\prec c$. Rule A at $x=c$, $w=z$ ($z-c$ odd) gives $c\prec z\iff c\prec c+1$, which is true; so $c\prec z$. Hence $q\prec c\prec z$.

**Case 1: $2q-z\in[\alpha,\beta]$.** Rule A at $x=q$, $w=z$ gives $q\prec z\iff q\prec q+1$, which holds.

**Case 2: $2q-z<\alpha$**, i.e. $z>2q-\alpha$. Among the four integers $\lceil(z+\alpha)/2\rceil,\dots,\lceil(z+\alpha)/2\rceil+3$ choose $c\equiv q+2\pmod4$. Then
* $2c\ge z+\alpha>2q$, so $c>q$, hence $c\ge q+2\ge\alpha+6$; and $z>2q-\alpha\ge q+4$;
* $2c\le z+\alpha+7\le\beta+q-1$, because $z\le\beta-4$ and $\alpha\le q-4$; hence $c\le\beta-2$ (as $q\le\beta-4$), $2c-q\in[c,\beta]$, and $2c-z\in[\alpha,\beta]$ (as $q<z$);
* $c$ 2-trails: zigzag ($g=2$) between the rungs $(q+2,q+4)$ and $(c,c+2)$ gives $c\prec c+2\iff q+2\prec q+4$; by the midpoint rule at $(q,q+2,q+4)$ this is equivalent to $q+2\prec q$, which is false since $q\prec q+2$.

The key step gives $q\prec z$.

**Case 3: $2q-z>\beta$**, i.e. $z<2q-\beta$. Then $2q>\beta+z\ge(q+4)+(\alpha+4)$, so $q>\alpha+8$, and $z<q$. Among $\lceil(\alpha+q)/2\rceil,\dots,\lceil(\alpha+q)/2\rceil+3$ choose $c\equiv q+2\pmod4$. Then
* $2c\ge\alpha+q>\alpha+z$, and $c\ge\alpha+5$;
* $2c\le\alpha+q+7\le\beta+z-1$, because $z\ge\alpha+4$ and $\beta\ge q+4$; hence $2c<2q$, so $c<q$ and $c\le q-2$; and $2c-q,\,2c-z\in[\alpha,\beta]$;
* $c$ 2-trails: zigzag between the rungs $(c,c+2)$ and $(q-2,q)$ gives $c\prec c+2\iff q-2\prec q$; the midpoint rule at $(q-2,q,q+2)$ and $q\prec q+2$ give $q\prec q-2$, so this is false.

The key step gives $q\prec z$. The three cases exhaust all $z$. $\square$

**Remarks.**
1. *Margin.* The proof needs margin $4$: the window of admissible centres must contain a full residue system mod $4$. The working notes and the computation referee report, from exhaustive enumeration and SAT computations (evidence, not formalized), that margin $3$ already suffices for all interval lengths tested, while margin $2$ fails for some lengths.
2. *Prior art.* As the scope referee observed, the Quarter Lemma is implied by Theorems 2.1 and 2.4 of A. Sharma, *Enumerating permutations that avoid three term arithmetic progressions*, Electron. J. Combin. 16 (2009), #R63. The two-flood proof above is independent of that paper; the derivation from Sharma's theorems is not formalized here.

## 4. Anchors

**Lemma 4.1 (anchor; refereed Lemma 0.2).** Let $\prec$ be admissible on $S$ and $a<w$ in $S$ with $2w-a\in S$. If $a\prec w$, then $2w-a\prec w$.

*Proof.* Otherwise $a\prec w\prec 2w-a$ is a monotone 3-AP. $\square$

**Lemma 4.2 (single anchor; refereed Lemma 3.1).** Let $\prec$ be admissible on $S$, $[\alpha,\beta]\subseteq S$ with $\beta\ge\alpha+8$, $y$ in the leading quarter ($y\prec y+1$, $y\prec y+2$), and $t\in S$ such that $z=2y-t$ has the trailing parity ($z+1\prec z$), with $y,z\in[\alpha+4,\beta-4]$. Then $y\prec t$.

*Proof.* The Quarter Lemma (local form) gives $y\prec z$; in particular $z\ne y$, so $t\ne y$. If $t<y<z$ and $t\prec y$, Lemma 4.1 gives $z\prec y$, a contradiction; so $y\prec t$. If $z<y<t$, the midpoint rule at $(z,y,t)$ turns $y\prec z$ into $y\prec t$. $\square$

Lemma 4.2 is not needed for Theorem 5.2 (it is the step behind Corollary Q of the working notes); it is formalized as `single_anchor`.

## 5. Theorem L\* for one anchor pair

**Lemma 5.1 (one link).** Let $\prec$ be admissible on $S$; let $e,e+1\in S$ and $y\in S$ with $e+1<y$, $e\prec y$ and $e+1\prec y$; let $[\alpha,\beta]\subseteq S$ contain $2y-e-1$ and $2y-e$ in its 4-interior, and let $[w,w+3]$ lie in its 4-interior. Then some $y'\in[w,w+3]$ satisfies $y'\prec y$.

*Proof.* The order restricted to $[\alpha,\beta]$ is admissible, and $\beta\ge w+7\ge\alpha+11$. The points $2y-e-1$ and $2y-e$ are consecutive, so by zigzag exactly one of them, $z=2y-t$ with $t\in\{e,e+1\}$, has the trailing parity ($z+1\prec z$). By Lemma 4.1 at $(t,y,z)$, $z\prec y$. In $[w,w+1]$ there is $u$ with $u\prec u+1$ (if $u=w$ fails, the midpoint rule at $(w,w+1,w+2)$ gives $w+1\prec w+2$). If $u\prec u+2$, put $y'=u$; otherwise $u+2\prec u$, the midpoint rule at $(u,u+2,u+4)$ gives $u+2\prec u+4$, and $u+2\prec u+3$ by zigzag; put $y'=u+2$. Then $y'\in[w,w+3]$, $y'\prec y'+1$, $y'\prec y'+2$, and the Quarter Lemma (local form) gives $y'\prec z$. So $y'\prec z\prec y$. $\square$

**Theorem 5.2 (Theorem L\*, one anchor pair).** Let $e,e+1\in S$ and let $[a_m,b_m]\subseteq S$ ($m\ge0$) satisfy, for every $m$,
$$a_m\ge m,\qquad b_m\ge a_m+11,\qquad a_{m+1}+e+5\le 2a_m+8,\qquad 2a_m+18\le b_{m+1}+e .$$
The last two conditions say $2y-t\in[a_{m+1}+4,b_{m+1}-4]$ for all $y\in[a_m+4,a_m+7]$ and $t\in\{e,e+1\}$. Then $S$ is not permutable.

*Proof.* Suppose $\prec$ is an admissible order of type $\omega$. Only finitely many elements precede $e$ or $e+1$; let $B$ bound them. Then $e+1\le B$, and every element of $S$ above $B$ comes after $e$ and $e+1$. For $m\ge B+1$ every element of $[a_m,b_m]$ is $\ge a_m\ge m>B$. Put $y_0=a_{B+1}+4$. Given $y_n\in[a_{B+1+n}+4,a_{B+1+n}+7]$, Lemma 5.1 with $[\alpha,\beta]=[a_{B+2+n},b_{B+2+n}]$ and $w=a_{B+2+n}+4$ gives $y_{n+1}\in[a_{B+2+n}+4,a_{B+2+n}+7]$ with $y_{n+1}\prec y_n$. (Its hypotheses: $y_n>B\ge e+1$; $2y_n-e-1\ge 2a_{B+1+n}+7-e\ge a_{B+2+n}+4$ and $2y_n-e\le2a_{B+1+n}+14-e\le b_{B+2+n}-4$; $w+7\le b_{B+2+n}$.) By induction $\operatorname{pos}(y_n)+n\le\operatorname{pos}(y_0)$ for all $n$, which is impossible for $n>\operatorname{pos}(y_0)$. $\square$

No choice principle and no lag hypothesis is used. The refereed Theorem 4.1 is the same argument for a finite family of odd-distance anchor pairs and arbitrary 4-windows; that generality is not formalized.

## 6. The B-link

Let $J_i=[r_i,r_{i+1}-1]$ be runs, $K=2k+1$, and let the *sliver* at $i$ be $\delta_i=2r_i-r_{i+K}$.

**Lemma 6.1 (B-link; refereed Lemma 5.1).** Let $J_i=[a,a'-1]$ with $a'-a\ge12$ and $J_{i+K-1}=[p,s-1]$ (so $s=r_{i+K}$ and $\delta_i=2a-s$). If
$$e-3-(s-p)\le\delta_i\le e-19,\qquad\text{i.e.}\qquad p+e\le2a+3\ \text{ and }\ 2a+19\le s+e,$$
then $W=[a+4,a+7]$ lies in the 4-interior of $J_i$, and $2y-t\in[p+4,s-5]$, the 4-interior of $J_{i+K-1}$, for all $y\in W$ and $t\in\{e,e+1\}$.

*Proof.* $a+7\le a'-5$. For $y\in W$ and $t\in\{e,e+1\}$: $2y-t\ge2a+8-e-1\ge p+4$ and $2y-t\le2a+14-e\le s-5$. $\square$

## 7. The exact ρ-partitions

Fix $k\ge1$ and $\varphi\in\mathbb R$, and put $K=2k+1$, $x_j=2^{\varphi+j/K}$ and $r_j=\lceil x_j\rceil$ for $j\in\mathbb N$.

**Lemma 7.1 (runs).**
* (i) For an integer $n\ge1$: $\lfloor K(\log_2n-\varphi)\rfloor=j\iff r_j\le n<r_{j+1}$.
* (ii) $r_j\ge1$.
* (iii) $2r_j-r_{j+K}\in\{0,1\}$.
* (iv) $r_{j+1}-r_j\to\infty$.

*Proof.* (i) $\lfloor y\rfloor=j$ iff $j\le y<j+1$. Since $K>0$ and $\log_2$ is increasing, $j\le K(\log_2n-\varphi)\iff\varphi+j/K\le\log_2n\iff x_j\le n\iff r_j\le n$ (as $n$ is an integer), and $K(\log_2n-\varphi)<j+1\iff\log_2n<\varphi+(j+1)/K\iff n<x_{j+1}\iff n<r_{j+1}$. (ii) $x_j>0$. (iii) $x_{j+K}=2x_j$, so $r_{j+K}=\lceil2x_j\rceil$, and $2\lceil x\rceil-2<2x\le2\lceil x\rceil$ gives $2\lceil x\rceil-1\le\lceil 2x\rceil\le2\lceil x\rceil$. (iv) $x_{j+1}-x_j=x_j(2^{1/K}-1)$, and for $j\ge KM$, $x_j\ge x_{KM}=2^Mx_0\ge Mx_0$; so for every $T$ there is $j_0$ with $x_{j+1}\ge x_j+T+1$ for $j\ge j_0$, and then $r_{j+1}\ge x_{j+1}\ge x_j+T+1>r_j+T$. $\square$

So, for natural indices, the run $J_j=[r_j,r_{j+1}-1]$ consists exactly of the $n\ge1$ with $\lfloor K(\log_2n-\varphi)\rfloor=j$, and has colour $j\bmod2$. (Runs with negative index, below $2^\varphi$, also belong to the classes; the proof does not use them.)

**Theorem 7.2 (refereed Theorem 5.2).** For $k\ge1$, $\varphi\in\mathbb R$ and $c\in\{0,1\}$, the class
$$A_c=\{n\ge1:\ \lfloor(2k+1)(\log_2n-\varphi)\rfloor\equiv c\pmod2\}$$
is not permutable. More generally, no $S\supseteq A_c$ is permutable.

*Proof.* Let $S\supseteq A_c$. By Lemma 7.1(i), every run $J_j$ with $j\equiv c$ lies in $S$.
* *Anchors.* By (iv) choose $j_0$ with $r_{j+1}\ge r_j+20$ for $j\ge j_0$, and $j_1\in\{j_0+1,j_0+2\}$ with $j_1\equiv c$. Put $e=r_{j_1}$. Then $e\ge r_{j_1-1}+20\ge20$ and $e+1<r_{j_1+1}$, so $e,e+1\in J_{j_1}\subseteq S$.
* *Chain.* By (iv) choose $j_2$ with $r_{j+1}\ge r_j+e+12$ for $j\ge j_2$, and $i_0\in\{j_2,j_2+1\}$ with $i_0\equiv c$. Put $a_m=r_{i_0+2km}$ and $b_m=r_{i_0+2km+1}-1$, so $[a_m,b_m]=J_{i_0+2km}$, of colour $c$ (as $2km$ is even). Then $a_m\ge 2km\ge m$ (the runs from $i_0$ on have length $\ge1$), and $b_m\ge a_m+11$.
* *Links.* For $i=i_0+2km$, apply Lemma 6.1 to $J_i$ and $J_{i+K-1}=J_{i+2k}$, with $a=r_i$, $a'=r_{i+1}$, $p=r_{i+2k}$, $s=r_{i+2k+1}$: $a'-a\ge e+12\ge12$; by (iii) $2a\le s+1$, so $2a+19\le s+20\le s+e$; and $p+e+12\le s\le2a$, so $p+e\le2a+3$. Lemma 6.1 gives exactly the last two conditions of Theorem 5.2 for $m$.

Theorem 5.2 shows that $S$ is not permutable. $\square$

The anchors are fixed and the chain uses only the B-links $J_i\to J_{i+K-1}$, whose slivers are $\delta_i\in\{0,1\}$. Each link moves $K-1=2k\ge2$ runs up (a little less than one octave), so the chain never returns to a run and $a_m\to\infty$.

## 8. Relation to earlier work

* **Kasel, arXiv:2609.02939.** Source of the ladder toolkit (zigzag and flood, Lemmas 23–26) that the Quarter Lemma uses, through Rules A and B.
* **Sharma, Electron. J. Combin. 16 (2009), #R63.** Theorems 2.1 and 2.4 imply the Quarter Lemma (Section 3, Remark 2).
* **Theorem I** ([Alex-lop/erdos-197-interval-gadget](https://github.com/Alex-lop/erdos-197-interval-gadget)). Its proof isolates Rules A and B and formalizes them; its Lean module is included here verbatim and supplies `Good.alt`, `Good.par`, `Good.lead_iff`, `Good.ruleA` and `Good.ruleB`.
* **Theorem R\*** ([Alex-lop/erdos-197-tower-obstruction](https://github.com/Alex-lop/erdos-197-tower-obstruction)) kills run colourings with ratios tending to $2$ but cannot reach runs of ratio below $7/4$; the runs of the exact ρ-partitions have ratio $2^{1/K}\le2^{1/3}<7/4$. Theorem 7.2 is complementary to it.
* In the project's working notes the exact ρ-partitions were earlier killed only under a bounded-lag hypothesis (an unrefereed note); Theorem 7.2 needs none. According to the scope referee, Theorem L\* and the lag-free kill of the exact ρ-partitions are new, while the Quarter Lemma follows from Sharma's theorems.

**What Theorem 7.2 does not reach.** It uses that every sliver $\delta_i=2r_i-r_{i+K}$ is $0$ or $1$. It says nothing about ρ-type run colourings whose boundaries drift, so that the slivers are unbounded (the working notes kill some of these, e.g. slivers bounded above or tending to $+\infty$, by the same chain with B-links or with links from the top of a run; those results are not formalized here, and mixed sign patterns with "dead-end" runs survive all the tools there), about log-periodic interval colourings with more arcs per period, or about non-interval colourings.

## 9. Lean formalization

`Erdos197Rho/Basic.lean` follows Sections 2–7; `Erdos197Interval/Basic.lean` is the Theorem I module, included verbatim.

* An order of an interval is an injective ranking $\sigma:\mathbb N\to\mathbb N$ ($x\prec y$ iff $\sigma x<\sigma y$); `Erdos197Interval.Good L R σ` is injectivity plus the midpoint rule on $[L,R]$, and `good_of_injOn` turns the hypotheses of `Erdos197Rho.quarter` into it. `phases` is Lemma 2.1, `quarter_good` the local form of the Quarter Lemma, and `quarter_thm` Lemma 3.1 in the form of `Challenge.lean`, with $\pi$ and $Q$ given by (P) and (Q).
* An order of type $\omega$ of $S$ is `Adm S ρ`: injectivity and the midpoint rule on $S$, plus "for every $N$ only finitely many elements have position $\le N$". `adm_of_enum` builds it from the positions $f^{-1}$ of an enumeration $f:\mathbb N\simeq S$ without monotone 3-term APs (formal-conjectures' predicate, unfolded). `good_of_adm` restricts it to an interval.
* `anchor` is Lemma 4.1, `single_anchor` Lemma 4.2, `link` Lemma 5.1, `chain` Theorem 5.2, `blink` Lemma 6.1.
* `rho_runs` is Lemma 7.1, with `Real.logb 2`, `Int.floor` and `Nat.ceil`; it is the only place where real numbers occur. `runs_int` is Theorem 7.2 for any integer run boundaries satisfying (ii)–(iv); `rho_adm`, `rho_sub` (any $S\supseteq A_c$) and `rho_thm` (the class itself) are Theorem 7.2.
* `quarter_thm` and `rho_thm` prove the statements of `Challenge.lean`, which `Solution.lean` restates as `Erdos197Rho.quarter` and `Erdos197Rho.main_result`.

The Lean statements use Lean's $\mathbb N=\{0,1,2,\dots\}$, as formal-conjectures does; the classes $A_c$ are defined with $n\ge1$ because $\log_20$ is undefined (Lean's `Real.logb 2 0 = 0`).

## 10. Verification history

The refereed text is `work/p197_m2_r3/rho/proof.md` of the project's working notes (not included in this repository). Its Quarter Lemma, Lemma 3.1, Corollary Q, Theorem L\*, Lemma 5.1 and Theorem 5.2 were checked by three adversarial AI referees, each with its own code, and none was refuted:

* *proof* (confidence 0.96): every step re-derived against Rules A and B of Theorem I; own brute force over all admissible orders of short intervals and own SAT encodings (Quarter Lemma, the link step of Theorem L\* for exact ρ-partitions with $k=1,2,3$ and several phases, with SAT controls) agree;
* *computation* (0.95): the Quarter Lemma at margins $4$ and $3$ checked exhaustively for interval lengths up to $63$ by independent programs, and by SAT beyond; Rules A and B checked exhaustively; Theorem-L\* link steps UNSAT on exact ρ-partitions; the B-link inequalities of Theorem 5.2 checked numerically up to $2^{60}$ for $K=3,\dots,9$ and six phases;
* *scope* (0.85): statements correct and honestly labelled; the Quarter Lemma follows from Sharma's Theorems 2.1 and 2.4 (credit added here); Theorem L\* and the exact-ρ kill are new as far as found.

The referees' computations are evidence for the informal proof and are not part of the formalization. This note is a rewrite; the introduction lists the parts that were not refereed, each mirrored by the Lean proof. The statements formalized here are proved by the Lean kernel. Neither the refereed text nor this note has been refereed by a human.
