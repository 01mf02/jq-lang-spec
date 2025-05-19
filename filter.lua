function dump(o)
   if type(o) == 'table' then
      local s = '{ '
      for k,v in pairs(o) do
         if type(k) ~= 'number' then k = '"'..k..'"' end
         s = s .. '['..k..'] = ' .. dump(v) .. ','
      end
      return s .. '} '
   else
      return tostring(o)
   end
end

function subst_math(text)
  return text
    -- insert negative space between non-space character ("%S") and ": "
    :gsub("(%S): ", "%1\\!: ")
    -- insert space after ";" when followed by " "
    :gsub("; ", ";\\; ")
    --:gsub(". ", ".\\, ")
    -- insert spaces around "|"
    :gsub(" | ", "\\;|\\;")
end

function RawInline(el)
  if el.format == "tex" and el.text:find("\\begin{align") == 1 then
    el.text = subst_math(el.text)
    return el
  end
end

function Math(el)
  el.text = subst_math(el.text)
  return el
end

function Table(el)
  set_table_id(el)
  return el
end

-- Transform citations that contain ":" to references.
--
-- This allows e.g. referencing tables via "@tab:foo".
-- This implements roughly the idea given in
-- <https://github.com/jgm/pandoc/issues/813#issuecomment-70423503>.
-- (However, note that this solution breaks when trying to reference
-- bibliographic sources that contain ":".)
function Cite(el)
  if #el.citations ~= 1 then return end
  local id = el.citations[1].id
  if not string.find(id, ":") then return end
  if FORMAT:match "latex" then
    return pandoc.RawInline("latex", "\\autoref{" .. id .. "}")
  else
    return pandoc.Link(id, "#" .. id)
  end
end

-- Transform divs with a single class to a LaTeX environment.
function Div(el)
  if #el.classes ~= 1 then return end
  local env = el.classes[1]
  local name = el.attributes["name"]
  if FORMAT:match "latex" then
    local label = el.identifier ~= "" and "\\label{" .. el.identifier .. "}" or ""
    local name = name and "[" .. name .. "]" or ""
    el.content:insert(1, pandoc.RawInline("latex", "\\begin{" .. env .. "}" .. name .. label))
    el.content:insert(#el.content + 1, pandoc.RawInline("latex", "\\end{"   .. env .. "}"))
    return el.content
  else
    local name = name and " (" .. name .. ")" or ""
    local head = pandoc.Emph(env:gsub("^%l", string.upper) .. name)
    local dl = pandoc.DefinitionList({{head, el.content}})
    return el.identifier ~= "" and pandoc.Div(dl, {id = el.identifier}) or dl
  end
end

function Pandoc(el)
  --print(dump(el))
end

-- If caption of input table ends with "{#...}",
-- remove that from caption and set table identifier.
--
-- E.g., if table caption is
-- "Foo. {#tab:foo}", then the caption becomes
-- "Foo. " and the identifier is set to "tab:foo".
-- This allows the table to be referenced.
function set_table_id(el)
  local caption = el.caption.long
  if #caption ~= 1 or caption[1].tag ~= "Plain" then return end
  local plain = caption[1].content
  local last = plain[#plain]
  if last.tag ~= "Str" then return end
  local _, _, id = string.find(last.text, "^{#(.-)}$")
  if id == nil then return end
  table.remove(plain, #plain)
  el.identifier = id
end
