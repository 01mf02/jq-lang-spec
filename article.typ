#let article(
  title: none,
  authors: (),
  abstract: [],
  doc
) = {
  text(17pt, title)

  par(authors.map(author => [
    #author.name \
    //#author.affiliation \
    #link("mailto:" + author.email)
  ]).join())

  par(justify: false)[
    *Abstract* \
    #abstract
  ]

  doc
}
