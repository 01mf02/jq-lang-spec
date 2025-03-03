#import "@preview/ctheorems:1.1.3": thmplain, thmrules

#let thm(x, y, ..args) = thmplain(x, y, inset: (left: 0em, right: 0em), ..args)
#let example = thm("example", "Example")
#let lemma = thm("theorem", "Lemma")
#let theorem = thm("theorem", "Theorem")
#let proof = thm("proof", "Proof",
  bodyfmt: body => [
    #body #h(1fr) $square$    // Insert QED symbol
  ]
).with(numbering: none)

#let or_ = $quad || quad$
#let app(..xs) = $#xs.pos().join($med$)$
#let lam(..xs) = $lambda #app(..xs). thick$
#let bind = $>#h(-0.5em)>#h(-1em / 6)=$
#let bindl = $class("binary", bind_S)$
#let bindr = $class("binary", bind_R)$
#let stream(..xs) = $angle.l #xs.pos().join($, $) angle.r$
#let var(x) = $\$#x$
#let ok(x) = $app("ok", #x)$
#let cartesian = math.op($circle.small$)
#let arith = math.op($dot.circle$)
#let mod = math.op($\%$)
#let aritheq = math.op($dot.circle#h(0pt)=$)
#let fold = math.op($phi.alt$)
#let update = $|#h(0pt)=$
#let alt = $slash.double$
#let alteq = math.op($alt#h(0pt)=$)
#let defas = $#h(0pt):$
#let defend = $; thick$

#let bot = math.class("normal", sym.bot)

#let qs(s) = $quote#h(0pt)#s#h(0pt)quote$
#let oat(k) = $.[#qs(k)]$
