-- exercises in "Type-Driven Development with Idris"
-- chapter 12, section 3

-- check that all functions are total
%default total

record Votes where
  constructor MkVotes
  upvotes : Integer
  downvotes : Integer

record Article where
  constructor MkArticle
  title : String
  url : String
  score : Votes

initPage : (title : String) -> (url : String) -> Article
initPage title url = MkArticle title url (MkVotes 0 0)

getScore : Article -> Integer
getScore a = let s = score a in (upvotes s) - (downvotes s)

badSite : Article
badSite = MkArticle "Bad Page" "http://example.com/bad" $ MkVotes 5 47

goodSite : Article
goodSite = MkArticle "Good Page" "http://example.com/good" $ MkVotes 101 7

addUpVote : Article -> Article
addUpVote = record { score->upvotes $= (+1) }

addDownVote : Article -> Article
addDownVote = record { score->downvotes $= (+1) }
