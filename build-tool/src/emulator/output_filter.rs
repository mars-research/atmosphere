//! Initial output filter.
//!
//! An `AsyncBufRead` wrapper that filters out initial boot outputs
//! from the emulator so they don't mess up our terminal.

use std::cmp::min;
use std::task::{Context, Poll};
use std::io::Result as IoResult;
use std::pin::Pin;

use tokio::io::{AsyncRead, AsyncBufRead, AsyncBufReadExt, Lines, ReadBuf};

/// A filter that suppresses initial boot outputs from the emulator.
pub struct InitialOutputFilter<R>
where
    R: AsyncBufRead + Unpin + Sized,
{
    state: Option<FilterState<R>>,
    write_buffer: Vec<u8>,
}

/// Internal state of the filter.
enum FilterState<R>
where
    R: AsyncBufReadExt + Unpin + Sized,
{
    /// We are suppressing the initial output.
    Suppress(Pin<Box<Lines<R>>>),

    /// We are passing through everything.
    Passthrough(Pin<Box<R>>),
}

impl<R> InitialOutputFilter<R>
where
    R: AsyncBufRead + Unpin + Sized,
{
    pub fn new(reader: R) -> Pin<Box<Self>> {
        let lines = reader.lines();
        let state = FilterState::Suppress(Box::pin(lines));

        Box::pin(Self {
            state: Some(state),
            write_buffer: "Booting: ".as_bytes().to_vec(),
        })
    }
}

impl<R> AsyncRead for InitialOutputFilter<R>
where
    R: AsyncBufRead + Unpin + Sized,
{
    fn poll_read(
        mut self: Pin<&mut Self>,
        cx: &mut Context<'_>,
        buf: &mut ReadBuf<'_>,
    ) -> Poll<IoResult<()>> {
        if !self.write_buffer.is_empty() {
            assert!(buf.remaining() != 0);

            let take = min(buf.remaining(), self.write_buffer.len());
            let remaining = self.write_buffer.split_off(take);
            buf.put_slice(&self.write_buffer);
            self.write_buffer = remaining;

            return Poll::Ready(Ok(()));
        }

        let mut unsuppress = false;

        match self.state.as_mut().unwrap() {
            FilterState::Suppress(lines) => {
                match lines.as_mut().poll_next_line(cx) {
                    Poll::Pending => {
                        return Poll::Pending;
                    }
                    Poll::Ready(Ok(None)) => {
                        // EOF
                        return Poll::Ready(Ok(()));
                    }
                    Poll::Ready(Err(e)) => {
                        return Poll::Ready(Err(e));
                    }
                    Poll::Ready(Ok(Some(line))) => {
                        if line.contains("SeaBIOS") {
                            // At BIOS
                            self.write_buffer.extend_from_slice(b"SeaBIOS... ");
                        } else if line.contains("Booting `") {
                            // Our kernel is booting!
                            unsuppress = true;
                            self.write_buffer.extend_from_slice(b"GRUB... ");
                        } else {
                            // Garbage
                            cx.waker().wake_by_ref();
                            return Poll::Pending;
                        }
                    }
                }
            }
            FilterState::Passthrough(buf_read) => {
                return buf_read.as_mut().poll_read(cx, buf);
            }
        }

        if unsuppress {
            let lines = self.state.take().unwrap();

            if let FilterState::Suppress(lines) = lines {
                let lines = Pin::into_inner(lines);
                let reader = lines.into_inner();
                self.state = Some(FilterState::Passthrough(Box::pin(reader)));

                cx.waker().wake_by_ref();
                return Poll::Pending;
            } else {
                unreachable!()
            }
        }

        // Emit our write buffer
        assert!(self.write_buffer.len() != 0);
        self.poll_read(cx, buf)
    }
}
