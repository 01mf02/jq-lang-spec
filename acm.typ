#let mainFont = "Libertinus Serif"
#let sfFont = "Libertinus Sans"

#let show-month(month) = (
  "January",
  "February",
  "March",
  "April",
  "May",
  "June",
  "July",
  "August",
  "September",
  "October",
  "November",
  "December"
).at(month - 1)

#let author-names(authors) = authors.map(author => author.name).join(", ", last: " and ")

#let author-address(author) = {
  author.name
  if author.at("email", default: none) != none [, #author.email]
}

#let show-author(author) = {
  text(fill: blue, font: sfFont, size: 11pt, upper(author.name))
  let affiliation = author.at("affiliation", default: none)
  if affiliation != none {
    text(font: mainFont, size: 9pt)[, #affiliation.institution, #affiliation.country]
  }
}

#let show-subconcept(priority, name) = {
  if priority >= 500 {
    strong(name)
  } else if priority >= 300 {
    emph(name)
  } else {
    name
  }
}

#let show-ccs(concept) = [
  #box(baseline: -50%, circle(radius: 1.25pt, fill: black)) *#concept.at(0)* $->$
  #concept.at(1).map(subconcept => show-subconcept(subconcept.at(0), subconcept.at(1))).join("; ")]

#let legal(pub) = [
  Permission to make digital or hard copies of all or part of this
  work for personal or classroom use is granted without fee provided
  that copies are not made or distributed for profit or commercial
  advantage and that copies bear this notice and the full citation on
  the first page. Copyrights for components of this work owned by
  others than ACM must be honored. Abstracting with credit is
  permitted. To copy otherwise, or republish, to post on servers or to
  redistribute to lists, requires prior specific permission
  and#h(.5pt)/or  a fee. Request permissions from
  permissions\@acm.org.\
  #sym.copyright #pub.year Association for Computing Machinery\
  0004-5411/2018/8-ART1 \$15.00\
  https:\/\/doi.org\/#pub.doi
]

#let total-pages = context {
  let total = counter(page).final().last()
  [#total page#if(total > 1) { [s] }]
}
#let even-page(loc) = calc.rem(loc.page(), 2) == 0

#let header(short, pub, loc) = {
  let article = if pub != none [#{pub.article}:]
  let article-page = [#article#counter(page).display()]
  if even-page(loc) [#article-page #h(1fr) #{short.authors}]
  else [#{short.title} #h(1fr) #article-page]
}

#let footer(pub) = if pub != none [
  #pub.journal-short,
  Vol. #pub.volume,
  No. #pub.number,
  Article #pub.article.
  Publication date: #show-month(pub.month) #pub.year.
]


#let acmart(
  // Currently supported formats are:
  //  - acmsmall
  format: "acmsmall",
  draft: false,
  
  // Title, subtitle, authors, abstract, ACM ccs, keywords
  title: "Title",
  title-short: none,
  subtitle: none,
  authors: (),
  authors-short: none,
  anonymous: false,
  abstract: none,
  ccs: none,
  keywords: none,

  pub: (
    journal: none,
    journal-short: none,
    volume: 1,
    number: 1,
    article: none,
    month: 5,
    year: 2023,
    doi: "XXXXXXX.XXXXXXX",
  ),

  copyright: pub => [
    Permission to make digital or hard copies of all or part of this
    work for personal or classroom use is granted without fee provided
    that copies are not made or distributed for profit or commercial
    advantage and that copies bear this notice and the full citation on
    the first page. Copyrights for components of this work owned by
    others than ACM must be honored. Abstracting with credit is
    permitted. To copy otherwise, or republish, to post on servers or to
    redistribute to lists, requires prior specific permission
    and#h(.5pt)/or  a fee. Request permissions from
    permissions\@acm.org.\
    #sym.copyright #pub.year Association for Computing Machinery\
    0004-5411/2018/8-ART1 \$15.00\
    https:\/\/doi.org\/#pub.doi
  ],

  body
) = {
  if anonymous {
    authors = ((name: "Anonymous Author(s)"),)
    authors-short = "Anon."
  }
  let short = (
    title: if title-short == none { title } else { title-short },
    authors: if authors-short == none { author-names(authors) } else { authors-short },
  )

  set par.line(numbering: n => text(red)[#n]) if draft

  // Set document metadata
  set document(title: title, author: authors.map(author => author.name))

  // Configure the page.
  set page(
    width:  6.75in,
    height: 10in,
    margin: (
      top: 58pt + 27pt,
      bottom: 39pt + 24pt,
      left: 46pt,
      right: 46pt
    ),
    header: text(size: 8pt, font: sfFont, context {
      if counter(page).get().first() > 1 { header(short, pub, here()) }
    }),
    footer: text(size: 8pt, context {
      align(if even-page(here()) { left } else { right }, footer(pub))
    }),
    header-ascent: 17pt,
    footer-descent: 24pt,
  )

  // title page
  {
    set text(size: 9pt)
    set par(justify: true, leading: 0.555em, spacing: 9.5pt)

    // Display title
    text(font: sfFont, size: 14.4pt, weight: "bold", title)
    v(7pt)

    authors.map(show-author).join("\n")
    if not(anonymous) {
      footnote(numbering: x => [#hide[0]], [#linebreak() #v(-1.5em) Authors' addresses: #authors.map(author-address).join("; ").])
    }
    footnote(numbering: x => [#hide[0]], (v(-1em), copyright(pub)).join())
    v(2.5pt)

    let ref-format = if pub != none [
      *ACM Reference Format:* \
      #author-names(authors).
      #pub.year.
      #title.
      #emph(pub.journal-short)
      #pub.volume,
      #pub.number,
      Article #pub.article (#show-month(pub.month) #pub.year),
      #total-pages.
      https:\/\/doi.org\/#pub.doi
    ]

    [
      #abstract

      CCS Concepts: #ccs.map(show-ccs).join("; ").

      Additional Key Words and Phrases: #keywords.join(", ")

      #ref-format
    ]

    v(1pt)
  }

  set text(font: mainFont, size: 10pt)

  set heading(numbering: "1.1")
  show heading: it => block(text(font: sfFont, size: 10pt, weight: "bold", {
    if it.numbering != none {
      counter(heading).display()
      box(width: 11pt)
    }
    upper(it.body)
  }))

  set par(
    justify: true,
    leading: 5.35pt,
    first-line-indent: 9.5pt,
    spacing: 5.35pt
  )

  body
}
