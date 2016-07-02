object Test {

  case class Point(x: Float, y: Float)

  val p = Point(15, 20.3)

  def add(p: Point, q: Point) = Point(p.x+ q.x, p.y+ q.y)
}
