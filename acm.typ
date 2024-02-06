#let mainFont = "Linux Libertine O"
#let sfFont = "Linux Biolinum O"

#let displayMonth(month) = (
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

#let authorsAddresses(authors) = {
  authors
    .map(author => {
      author.name
      if author.at("email", default: none) != none [, #author.email]
    })
    .join("; ")
}

// Display authors
#let displayAuthors(authors) = {
  set par(leading: 5.7pt)
  let displayAuthor(author) = [#text(font: sfFont, size: 11pt, upper(author.name))]
  let displayAuthors(authors) = authors.map(displayAuthor).join(", ", last: " and ")

  let displayAffiliation(affiliation) = [,#text(font: mainFont, size: 9pt)[
    #affiliation.institution, #affiliation.country]\
  ]
  par({
    let affiliation = none
    let currentAuthors = ()
    for author in authors {
      // if affiliation changes, print author list and affiliation
      if author.affiliation != affiliation and affiliation != none {
        displayAuthors(currentAuthors)
        displayAffiliation(affiliation)
        currentAuthors = ()
      }
      currentAuthors.push(author)
      affiliation = author.affiliation
    }
    displayAuthors(currentAuthors)
    if affiliation != none {
      displayAffiliation(affiliation)
    }
    footnote([Authors' addresses: #authorsAddresses(authors).])
  })
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

#let show-ccs(concept) = {
  box(baseline: -50%, circle(radius: 1.25pt, fill: black)); [ ]
  strong(concept.at(0)); [ ]
  sym.arrow.r; [ ]
  concept.at(1).map(subconcept => show-subconcept(subconcept.at(0), subconcept.at(1))).join("; ")
}

#let legal(acm) = [
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
  #sym.copyright #acm.year Association for Computing Machinery\
  0004-5411/2018/8-ART1 \$15.00\
  https:\/\/doi.org\/#acm.doi
]

#let even-page(loc) = calc.rem(loc.page(), 2) == 0

#let acmart(
  // Currently supported formats are:
  //  - acmsmall
  format: "acmsmall",
  
  // Title, subtitle, authors, abstract, ACM ccs, keywords
  title: "Title",
  subtitle: none,
  shorttitle: none,
  authors: (),
  shortauthors: none,
  abstract: none,
  ccs: none,
  keywords: none,

  acm: (
    journal: none,
    volume: 1,
    number: 1,
    article: none,
    month: 5,
    year: 2023,
    doi: "XXXXXXX.XXXXXXX",
  ),

  body
) = {
  let journal = if acm.journal == "JACM" {
    (
      name: "Journal of the ACM",
      nameShort: "J. ACM"
    )
  } else {
    none
  }

  if shorttitle == none {
    shorttitle = title
  }

  if shortauthors == none {
    shortauthors = authors.map(author => author.name).join(", ", last: " and ")
  }

  let footer = [
    #journal.nameShort,
    Vol. #acm.volume,
    No. #acm.number,
    Article #acm.article.
    Publication date: #displayMonth(acm.month) #acm.year.
  ]

  let header(loc) = {
    let article_page = [#acm.article:#counter(page).display()]
    if even-page(loc) [#article_page #h(1fr) #shortauthors]
    else [#shorttitle #h(1fr) #article_page]
  }

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
    header: text(size: 8pt, font: sfFont, locate(loc => if loc.page() > 1 { header(loc) })),
    footer: text(size: 8pt, locate(loc => align(if even-page(loc) { left } else { right }, footer))),
    header-ascent: 17pt,
    footer-descent: 24pt,
  )

  set text(font: mainFont, size: 10pt)
  
  // title page
  {
    set par(justify: true, leading: 0.555em)
    show par: set block(below: 0pt)

    // Display title
    par(text(font: sfFont, size: 14.4pt, weight: "bold", title))
    v(16.5pt)

    displayAuthors(authors)
    v(12pt)

    // Display abstract
    par(text(size: 9pt, abstract))
    v(9.5pt)

    // Display CSS concepts:
    par(text(size: 9pt, [CCS Concepts: #ccs.map(c => show-ccs(c)).join("; ").]))
    v(9.5pt)

    // Display keywords
    par(text(size: 9pt)[Additional Key Words and Phrases: #keywords.join(", ")])
    v(9.5pt)

    // Display ACM reference format
    par(text(size: 9pt)[
      #strong[ACM Reference Format:]\
      #authors.map(author => author.name).join(", ", last: " and ").
      #acm.year.
      #title.
      #emph(journal.nameShort)
      #acm.volume,
      #acm.number,
      Article #acm.article (#displayMonth(acm.month) #acm.year),
      #counter(page).display((..nums) => [
        #nums.pos().last() page#if(nums.pos().last() > 1) { [s] }.
      ],both: true)
      https:\/\/doi.org\/#acm.doi
      #footnote(legal(acm))
    ])
    v(1pt)
  }

  set heading(numbering: (..n) => [#n.pos().first()~~~])
  show heading: it => {
    set text(font: sfFont, size: 10pt, weight: "bold")
    upper(it)
    v(9pt - 0.555em)
  }

  set par(
    justify: true,
    leading: 5.35pt,
    first-line-indent: 9.5pt)
  show par: set block(below: 5.35pt)

  body
}
