#import "@preview/ctheorems:1.1.0": thmplain, thmrules

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
#let stream(..xs) = $angle.l #xs.pos().join($, $) angle.r$
#let var(x) = $\$#x$
#let cartesian = math.op($circle.small$)
#let arith = math.op($dot.circle$)
#let mod = math.op($\%$)
#let aritheq = math.op($dot.circle#h(0pt)=$)
#let fold = math.op($phi.alt$)
#let update = $models$
#let alt = $slash.double$
#let alteq = math.op($alt#h(0pt)=$)

#let qs(s) = $quote #s quote$
#let oat(k) = $.[#qs(k)]$
