pub enum Either<L, R> {
    Left(Left<L>),
    Right(Right<R>),
}

pub struct Left<T>(pub T);
pub struct Right<T>(pub T);
