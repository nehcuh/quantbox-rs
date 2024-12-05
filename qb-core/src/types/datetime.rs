//! Date and time types for the QuantBox system.
//!
//! This module provides a set of types and traits for handling dates and times
//! in a way that is both efficient and safe. The main types are:
//!
//! - `QBDate`: A compact date representation using YYYYMMDD format
//! - `QBTime`: A high-precision time representation
//! - `QBDateTime`: A combination of date and time
//! - `QBDateRange`: An iterator over a range of dates
//!
//! All date operations are checked to ensure they fall within the valid range
//! of 1900-01-01 to 3000-12-31.

use chrono::{Datelike, Duration, NaiveDate, Timelike};
use serde::{Deserialize, Serialize};
use std::borrow::Cow;
use std::cmp::{Ord, PartialOrd};
use std::collections::HashMap;
use std::fs;
use std::ops::Sub;
use std::sync::OnceLock;
use toml::Value;

pub use crate::errors::DateErrorKind;
pub use crate::{QBError, QBResult};

/// A compact date representation using YYYYMMDD format internally.
///
/// The date is stored as a u32 in the format YYYYMMDD, which allows for:
/// - Efficient storage (4 bytes)
/// - Easy comparison operations
/// - Simple conversion to/from integer format
///
/// Valid date range is from 1900-01-01 to 3000-12-31.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct QBDate(u32);

/// A high-precision time representation using nanosecond precision.
///
/// The time is stored as a u64 in the format HHmmss_nnn_nnn_nnn, which provides:
/// - Nanosecond precision
/// - Efficient storage (8 bytes)
/// - Easy comparison operations
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct QBTime(u64);

/// A complete date and time representation.
///
/// Combines QBDate and QBTime to provide full datetime functionality.
#[derive(Debug, PartialEq, Eq)]
pub struct QBDateTime {
    date: QBDate,
    time: QBTime,
}

impl PartialOrd for QBTime {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for QBTime {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.as_u64().cmp(&other.as_u64())
    }
}

impl PartialOrd for QBDateTime {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for QBDateTime {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match self.date.cmp(&other.date) {
            std::cmp::Ordering::Equal => self.time.cmp(&other.time),
            ord => ord,
        }
    }
}

impl QBDateTime {
    pub fn new<D: IntoQBDate, T: IntoQBTime>(date: D, time: T) -> QBResult<Self> {
        Ok(Self {
            date: date.into_qbdate()?,
            time: time.into_qbtime()?,
        })
    }

    pub fn date(&self) -> QBDate {
        self.date
    }

    pub fn time(&self) -> QBTime {
        self.time
    }

    pub fn year(&self) -> u32 {
        self.date.year()
    }

    pub fn month(&self) -> u32 {
        self.date.month()
    }

    pub fn day(&self) -> u32 {
        self.date.day()
    }

    pub fn hours(&self) -> u32 {
        self.time.hours()
    }

    pub fn minutes(&self) -> u32 {
        self.time.minutes()
    }

    pub fn seconds(&self) -> u32 {
        self.time.seconds()
    }

    pub fn nanos(&self) -> u32 {
        self.time.nanos()
    }
}

/// An iterator over a range of dates.
///
/// This struct provides a way to iterate over a range of dates, either forward
/// or backward. The iteration is inclusive of both start and end dates.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct QBDateRange {
    current: QBDate,
    end: QBDate,
    forward: bool,
}

impl QBDateRange {
    /// Creates a new date range with automatic direction detection.
    ///
    /// The direction is determined by comparing start and end dates:
    /// - If start > end, iterates backward
    /// - If start <= end, iterates forward
    ///
    /// # Arguments
    /// * `start` - The starting date
    /// * `end` - The ending date
    ///
    /// # Returns
    /// * `Some(QBDateRange)` if both dates are valid
    /// * `None` if either date is invalid
    pub fn new<T: IntoQBDate + Copy + PartialOrd>(start: T, end: T) -> Option<Self> {
        if let (Ok(start), Ok(end)) = (start.into_qbdate(), end.into_qbdate()) {
            if start > end {
                Some(Self {
                    current: start,
                    end,
                    forward: false,
                })
            } else {
                Some(Self {
                    current: start,
                    end,
                    forward: true,
                })
            }
        } else {
            None
        }
    }

    /// Creates a new date range with explicit direction control.
    ///
    /// # Arguments
    /// * `start` - The starting date
    /// * `end` - The ending date
    /// * `direction` - If true, iterates forward; if false, iterates backward
    ///
    /// # Returns
    /// * `Some(QBDateRange)` if both dates are valid
    /// * `None` if either date is invalid
    pub fn new_with_direction<T: IntoQBDate + Copy + PartialOrd>(
        start: T,
        end: T,
        direction: bool,
    ) -> Option<Self> {
        if let (Ok(start), Ok(end)) = (start.into_qbdate(), end.into_qbdate()) {
            Some(Self {
                current: start,
                end,
                forward: direction,
            })
        } else {
            None
        }
    }
}

impl Iterator for QBDateRange {
    type Item = QBDate;
    fn next(&mut self) -> Option<Self::Item> {
        if !self.forward || self.current > self.end {
            return None;
        }
        let current = self.current;
        self.current = self.current.add_days(1).unwrap();
        Some(current)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = if self.current > self.end {
            0
        } else {
            self.end
                .to_naive_date()
                .unwrap()
                .sub(self.current.to_naive_date().unwrap())
                .num_days() as usize
        };
        (remaining, Some(remaining))
    }
}

impl DoubleEndedIterator for QBDateRange {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.forward || self.current < self.end {
            return None;
        }

        let current = self.current;
        self.current = self.current.sub_days(1).unwrap();
        Some(current)
    }
}

/// Trait for types that can be converted into a QBDate.
///
/// This trait enables generic conversion from various types into QBDate,
/// including numeric types and string representations.
///
/// # Examples
///
/// ```
/// # use qb_core::types::datetime::QBDate;
/// let date = QBDate::new(20230101).unwrap();
/// let date = QBDate::new("2023-01-01").unwrap();
/// ```
pub trait IntoQBDate {
    /// Converts the implementing type into a QBDate
    fn into_qbdate(self) -> QBResult<QBDate>;
}

impl PartialOrd for QBDate {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(&other))
    }
}

impl Ord for QBDate {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.cmp(&other.0)
    }
}

impl QBDate {
    /// Creates a new QBDate from any type that implements IntoQBDate.
    ///
    /// # Arguments
    /// * `date` - A value that can be converted into a QBDate
    ///
    /// # Returns
    /// * `Ok(QBDate)` if the conversion is successful
    /// * `Err` if the date is invalid or out of range
    pub fn new<T: IntoQBDate>(date: T) -> QBResult<Self> {
        date.into_qbdate()
    }

    /// Creates a new QBDate from a u32 in YYYYMMDD format.
    ///
    /// # Arguments
    /// * `date` - A date in YYYYMMDD format (e.g., 20230101 for January 1, 2023)
    ///
    /// # Returns
    /// * `Ok(QBDate)` if the date is valid
    /// * `Err` if the date is invalid or out of range
    ///
    /// # Examples
    ///
    /// ```
    /// # use qb_core::types::datetime::QBDate;
    /// let date = QBDate::from_u32(20230101).unwrap();
    /// assert_eq!(date.year(), 2023);
    /// assert_eq!(date.month(), 1);
    /// assert_eq!(date.day(), 1);
    /// ```
    pub fn from_u32(date: u32) -> QBResult<Self> {
        let year = date / 10000;
        let month = (date - year * 10000) / 100;
        let day = date % 100;

        // Validate date range
        if year < 1900 || year > 3000 {
            return Err(QBError::DateError {
                kind: DateErrorKind::OutofRange,
                details: format!("Only support year between 1900 to 3000"),
            });
        }

        // Validate month
        if month < 1 || month > 12 {
            return Err(QBError::DateError {
                kind: DateErrorKind::OutofRange,
                details: format!("Error month been extracted: {month}"),
            });
        }

        // Validate day
        if day < 1 || day > get_days_in_month(year, month) {
            return Err(QBError::DateError {
                kind: DateErrorKind::OutofRange,
                details: format!("Error day been extracted: {day}"),
            });
        }

        Ok(Self(date))
    }

    /// Creates a new QBDate from a u32 in YYYYMMDD format but without value checking
    pub fn from_u32_unchecked(date: u32) -> QBResult<Self> {
        Ok(Self(date))
    }

    /// Converts chrono::NaiveDate into QBDate.
    ///
    /// # Arguments
    /// * `date` - A NaiveDate instance
    ///
    /// # Returns
    /// * `Ok(QBDate)` if the date is within valid range
    /// * `Err` if the date is out of range
    pub fn from_naive_date(date: NaiveDate) -> QBResult<Self> {
        date.into_qbdate()
    }

    /// Converts QBDate into chrono::NaiveDate.
    ///
    /// # Returns
    /// * `Ok(NaiveDate)` if the conversion is successful
    /// * `Err` if the date is invalid
    pub fn to_naive_date(&self) -> QBResult<NaiveDate> {
        NaiveDate::from_ymd_opt(self.year() as i32, self.month(), self.day()).ok_or(
            QBError::DateError {
                kind: DateErrorKind::Invalid,
                details: format!("Invalid date {self}"),
            },
        )
    }

    /// Returns the year component of the date.
    ///
    /// # Returns
    /// A value between 1900 and 3000
    pub fn year(self) -> u32 {
        self.0 / 10000
    }

    /// Returns the month component of the date.
    ///
    /// # Returns
    /// A value between 1 and 12
    pub fn month(self) -> u32 {
        (self.0 - self.year() * 10000) / 100
    }

    /// Returns the day component of the date.
    ///
    /// # Returns
    /// A value between 1 and 31, depending on the month
    pub fn day(self) -> u32 {
        self.0 % 100
    }

    /// Returns the internal u32 value in YYYYMMDD format.
    pub fn as_u32(self) -> u32 {
        self.0
    }

    /// Returns today's date
    ///
    /// # Examples
    /// ```
    /// use qb_core::types::datetime::QBDate;
    /// let today = QBDate::today();
    /// ```
    pub fn today() -> QBResult<Self> {
        let today = chrono::Local::now().date_naive();
        Self::from_naive_date(today)
    }

    /// Returns yesterday's date
    ///
    /// # Examples
    /// ```
    /// use qb_core::types::datetime::QBDate;
    /// let yesterday = QBDate::yesterday();
    /// ```
    pub fn yesterday() -> QBResult<Self> {
        Self::today()?.sub_days(1)
    }

    /// Returns tomorrow's date
    ///
    /// # Examples
    /// ```
    /// use qb_core::types::datetime::QBDate;
    /// let tomorrow = QBDate::tomorrow();
    /// ```
    pub fn tomorrow() -> QBResult<Self> {
        Self::today()?.add_days(1)
    }

    /// Creates an iterator over a date range(inclusive)
    pub fn range(start: QBDate, end: QBDate) -> QBDateRange {
        QBDateRange {
            current: start,
            end,
            forward: true,
        }
    }

    pub fn add_days(&self, days: u32) -> QBResult<QBDate> {
        let naive = self.to_naive_date()?;
        (naive + Duration::days(days as i64)).into_qbdate()
    }

    pub fn sub_days(&self, days: u32) -> QBResult<QBDate> {
        let naive = self.to_naive_date()?;
        (naive - Duration::days(days as i64)).into_qbdate()
    }

    pub fn add_months(&self, months: u32) -> QBResult<QBDate> {
        let naive = self.to_naive_date()?;
        let year = naive.year() + (months / 12) as i32;
        let month = naive.month() as i32 + (months % 12) as i32;
        let year = if month > 12 { year + 1 } else { year };
        let month = if month > 12 { month - 12 } else { month };
        let day = naive.day();
        let max_day = NaiveDate::from_ymd_opt(year, month as u32, 1)
            .unwrap()
            .with_month(month as u32 + 1)
            .unwrap_or_else(|| NaiveDate::from_ymd_opt(year + 1, 1, 1).unwrap())
            .pred_opt()
            .unwrap()
            .day();
        let day = std::cmp::min(day, max_day);

        NaiveDate::from_ymd_opt(year, month as u32, day)
            .ok_or(QBError::DateError {
                kind: DateErrorKind::Invalid,
                details: format!("Subtraction {months} would get invalid date"),
            })?
            .into_qbdate()
    }

    pub fn sub_months(&self, months: u32) -> QBResult<QBDate> {
        let naive = self.to_naive_date()?;
        let year = naive.year() - (months / 12) as i32;
        let month = naive.month() as i32 - (months % 12) as i32;
        let year = if month < 1 { year - 1 } else { year };
        let month = if month < 1 { month + 12 } else { month };
        let day = naive.day();
        let max_day = NaiveDate::from_ymd_opt(year, month as u32, 1)
            .unwrap()
            .with_month(month as u32 + 1)
            .unwrap_or_else(|| NaiveDate::from_ymd_opt(year + 1, 1, 1).unwrap())
            .pred_opt()
            .unwrap()
            .day();
        let day = std::cmp::min(day, max_day);

        NaiveDate::from_ymd_opt(year, month as u32, day)
            .ok_or(QBError::DateError {
                kind: DateErrorKind::Invalid,
                details: format!("Subtraction {months} would get invalid date"),
            })?
            .into_qbdate()
    }

    /// Returns true if the date falls on a weekend (Saturday or Sunday)
    pub fn is_weekend(self) -> bool {
        let naive = self.to_naive_date().unwrap();
        let weekday = naive.weekday();
        weekday == chrono::Weekday::Sat || weekday == chrono::Weekday::Sun
    }

    /// Returns true if the date falls on a weekday (Monday through Friday).
    pub fn is_weekday(self) -> bool {
        !self.is_weekend()
    }

    /// Add years to the date.
    ///
    /// This method handles leap years correctly. If the original date is
    /// February 29 and the target year is not a leap year, it will return
    /// February 28 instead.
    ///
    /// # Arguments
    /// * `years` - Number of years to add
    ///
    /// # Returns
    /// * `Ok(QBDate)` if the resulting date is valid
    /// * `Err` if the resulting date would be out of range
    pub fn add_years(&self, years: u32) -> QBResult<Self> {
        let naive = self.to_naive_date()?;
        let new_year = naive.year() + years as i32;
        if new_year < 1900 || new_year > 3000 {
            return Err(QBError::DateError {
                kind: DateErrorKind::OutofRange,
                details: format!("Year {new_year} is out of range (1900-3000)"),
            });
        }

        // Handle Feb 29 in non-leap years
        let month = naive.month();
        let day = naive.day();
        if month == 2 && day == 29 && !is_leap_year(new_year as u32) {
            NaiveDate::from_ymd_opt(new_year, 2, 28)
                .ok_or(QBError::DateError {
                    kind: DateErrorKind::Invalid,
                    details: format!("Invalid date after adding {years} years"),
                })?
                .into_qbdate()
        } else {
            NaiveDate::from_ymd_opt(new_year, month, day)
                .ok_or(QBError::DateError {
                    kind: DateErrorKind::Invalid,
                    details: format!("Invalid date after adding {years} years"),
                })?
                .into_qbdate()
        }
    }

    /// Subtract years from the date.
    ///
    /// This method handles leap years correctly. If the original date is
    /// February 29 and the target year is not a leap year, it will return
    /// February 28 instead.
    ///
    /// # Arguments
    /// * `years` - Number of years to subtract
    ///
    /// # Returns
    /// * `Ok(QBDate)` if the resulting date is valid
    /// * `Err` if the resulting date would be out of range
    pub fn sub_years(&self, years: u32) -> QBResult<Self> {
        let naive = self.to_naive_date()?;
        let new_year = naive.year() - years as i32;
        if new_year < 1900 || new_year > 3000 {
            return Err(QBError::DateError {
                kind: DateErrorKind::OutofRange,
                details: format!("Year {new_year} is out of range (1900-3000)"),
            });
        }

        // Handle Feb 29 in non-leap years
        let month = naive.month();
        let day = naive.day();
        if month == 2 && day == 29 && !is_leap_year(new_year as u32) {
            NaiveDate::from_ymd_opt(new_year, 2, 28)
                .ok_or(QBError::DateError {
                    kind: DateErrorKind::Invalid,
                    details: format!("Invalid date after subtracting {years} years"),
                })?
                .into_qbdate()
        } else {
            NaiveDate::from_ymd_opt(new_year, month, day)
                .ok_or(QBError::DateError {
                    kind: DateErrorKind::Invalid,
                    details: format!("Invalid date after subtracting {years} years"),
                })?
                .into_qbdate()
        }
    }

    /// Format the date according to the specified format string.
    ///
    /// The format string follows the chrono crate's format syntax.
    /// See [chrono::format::strftime](https://docs.rs/chrono/latest/chrono/format/strftime/index.html)
    /// for the full list of format specifiers.
    ///
    /// # Arguments
    /// * `fmt` - The format string
    ///
    /// # Returns
    /// * `Ok(String)` containing the formatted date
    /// * `Err` if the date is invalid
    ///
    /// # Examples
    ///
    /// ```
    /// # use qb_core::types::datetime::QBDate;
    /// let date = QBDate::from_u32(20230415).unwrap();
    /// assert_eq!(date.format("%Y-%m-%d").unwrap(), "2023-04-15");
    /// assert_eq!(date.format("%d/%m/%Y").unwrap(), "15/04/2023");
    /// ```
    pub fn format(&self, fmt: &str) -> QBResult<String> {
        self.to_naive_date()
            .map(|date| date.format(fmt).to_string())
    }

    /// Parse a date string according to the specified format.
    ///
    /// The format string follows the chrono crate's format syntax.
    /// See [chrono::format::strftime](https://docs.rs/chrono/latest/chrono/format/strftime/index.html)
    /// for the full list of format specifiers.
    ///
    /// # Arguments
    /// * `date_str` - The date string to parse
    /// * `fmt` - The format string
    ///
    /// # Returns
    /// * `Ok(QBDate)` if parsing succeeds
    /// * `Err` if parsing fails or the date is invalid
    ///
    /// # Examples
    ///
    /// ```
    /// # use qb_core::types::datetime::QBDate;
    /// let date = QBDate::parse("2023-04-15", "%Y-%m-%d").unwrap();
    /// assert_eq!(date.as_u32(), 20230415);
    /// ```
    pub fn parse(date_str: &str, fmt: &str) -> QBResult<Self> {
        NaiveDate::parse_from_str(date_str, fmt)
            .map_err(|_| QBError::DateError {
                kind: DateErrorKind::ParseError,
                details: format!("Failed to parse '{date_str}' with format '{fmt}'"),
            })?
            .into_qbdate()
    }
}

pub trait IntoQBTime {
    fn into_qbtime(self) -> QBResult<QBTime>;
}

// Implement for u64
impl IntoQBTime for u64 {
    fn into_qbtime(self) -> QBResult<QBTime> {
        QBTime::from_u64(self)
    }
}

// Implement for String
impl IntoQBTime for String {
    fn into_qbtime(self) -> QBResult<QBTime> {
        self.as_str().into_qbtime()
    }
}

// Implement for &str
// 12:32:21
impl IntoQBTime for &str {
    fn into_qbtime(self) -> QBResult<QBTime> {
        self.replace(":", "")
            .replace(" ", "")
            .replace(".", "")
            .parse::<u64>()
            .map_err(|_| QBError::DateError {
                kind: DateErrorKind::ParseError,
                details: format!("Failed to parse {} into QBTime", self),
            })?
            .into_qbtime()
    }
}

impl IntoQBTime for Cow<'_, str> {
    fn into_qbtime(self) -> QBResult<QBTime> {
        self.as_ref()
            .replace(":", "")
            .replace(" ", "")
            .parse::<u64>()
            .map_err(|_| QBError::DateError {
                kind: DateErrorKind::ParseError,
                details: format!("Failed to parse {} into QBTime", self),
            })?
            .into_qbtime()
    }
}

impl IntoQBTime for QBTime {
    fn into_qbtime(self) -> QBResult<QBTime> {
        Ok(self)
    }
}

impl QBTime {
    /// Creates a new QBTime from a u64 timestamp.
    ///
    /// This is a convenience wrapper around `from_u64` that provides a more intuitive constructor name.
    /// The input timestamp should follow the same format as `from_u64`.
    ///
    /// # Arguments
    /// * `time` - A u64 timestamp in the format HHMMSS\[nnnnnnnnn\] where:
    ///   - HH: Hours (00-23)
    ///   - MM: Minutes (00-59)
    ///   - SS: Seconds (00-59)
    ///   - nnnnnnnnn: Optional nanoseconds (000000000-999999999)
    ///
    /// # Returns
    /// * `Ok(QBTime)` if the timestamp is valid
    /// * `Err` if the timestamp contains invalid time components
    ///
    /// # Examples
    /// ```
    /// # use qb_core::types::datetime::QBTime;
    /// // Create time 14:30:00
    /// let time = QBTime::new(143000000000000).unwrap();
    /// assert_eq!(time.hours(), 14);
    /// assert_eq!(time.minutes(), 30);
    /// assert_eq!(time.seconds(), 0);
    /// assert_eq!(time.nanos(), 0);
    /// ```
    pub fn new(time: u64) -> QBResult<Self> {
        Self::from_u64(time)
    }
    /// Creates a new QBTime from a u64 with specific precision levels:
    /// - HH (2 digits): Hours only
    /// - HHMM (4 digits): Hours and minutes
    /// - HHMMSS (6 digits): Hours, minutes and seconds
    /// - HHMMSSmmm (9 digits): Including milliseconds
    /// - HHMMSSuuu_uuu (12 digits): Including microseconds
    /// - HHMMSSnnn_nnn_nnn (15 digits): Including nanoseconds
    ///
    /// # Arguments
    /// * `time` - Time in one of the supported formats
    ///
    /// # Returns
    /// * `Ok(QBTime)` if the time is valid
    /// * `Err` if the time is invalid or format not supported
    ///
    /// # Examples
    /// ```
    /// # use qb_core::types::datetime::QBTime;
    /// let hour = QBTime::from_u64(23).unwrap();              // 23:00:00.000000000
    /// let minute = QBTime::from_u64(2359).unwrap();          // 23:59:00.000000000
    /// let second = QBTime::from_u64(235959).unwrap();        // 23:59:59.000000000
    /// let milli = QBTime::from_u64(235959123).unwrap();      // 23:59:59.123000000
    /// let micro = QBTime::from_u64(235959123456).unwrap();   // 23:59:59.123456000
    /// let nano = QBTime::from_u64(235959123456789).unwrap(); // 23:59:59.123456789
    /// ```
    pub fn from_u64(time: u64) -> QBResult<Self> {
        let (hours, minutes, seconds, nanos) = match time.to_string().len() {
            // HH format
            2 => {
                if time > 23 {
                    return Err(QBError::DateError {
                        kind: DateErrorKind::OutofRange,
                        details: format!("Hours must be between 0-23, got {time}"),
                    });
                }
                (time, 0, 0, 0)
            }

            // HHMM format
            4 => {
                let hours = time / 100;
                let minutes = time % 100;
                (hours, minutes, 0, 0)
            }

            // HHMMSS format
            6 => {
                let hours = time / 10000;
                let minutes = (time / 100) % 100;
                let seconds = time % 100;
                (hours, minutes, seconds, 0)
            }

            // HHMMSSmmm format (milliseconds)
            9 => {
                let millis = time % 1000;
                let time = time / 1000;
                let seconds = time % 100;
                let minutes = (time / 100) % 100;
                let hours = time / 10000;
                (hours, minutes, seconds, millis * 1_000_000)
            }

            // HHMMSSuuu_uuu format (microseconds)
            12 => {
                let micros = time % 1_000_000;
                let time = time / 1_000_000;
                let seconds = time % 100;
                let minutes = (time / 100) % 100;
                let hours = time / 10000;
                (hours, minutes, seconds, micros * 1_000)
            }

            // HHMMSSnnn_nnn_nnn format (nanoseconds)
            15 => {
                let nanos = time % 1_000_000_000;
                let time = time / 1_000_000_000;
                let seconds = time % 100;
                let minutes = (time / 100) % 100;
                let hours = time / 10000;
                (hours, minutes, seconds, nanos)
            }

            // Invalid number of digits
            _ => {
                return Err(QBError::DateError {
                    kind: DateErrorKind::Invalid,
                    details: format!(
                        "Unsupported time format: {time}. Must be 2, 4, 6, 9, 12 or 15 digits"
                    ),
                })
            }
        };

        // Validate hours
        if hours > 23 {
            return Err(QBError::DateError {
                kind: DateErrorKind::OutofRange,
                details: format!("Hours must be between 0-23, got {hours}"),
            });
        }

        // Validate minutes
        if minutes > 59 {
            return Err(QBError::DateError {
                kind: DateErrorKind::OutofRange,
                details: format!("Minutes must be between 0-59, got {minutes}"),
            });
        }

        // Validate seconds
        if seconds > 59 {
            return Err(QBError::DateError {
                kind: DateErrorKind::OutofRange,
                details: format!("Seconds must be between 0-59, got {seconds}"),
            });
        }

        // Construct final time value
        let final_time = (hours * 10000 + minutes * 100 + seconds) * 1_000_000_000 + nanos;
        Ok(Self(final_time))
    }

    // Helper methods for accessing components
    pub fn hours(&self) -> u32 {
        ((self.0 / 1_000_000_000) / 10000) as u32
    }

    pub fn minutes(&self) -> u32 {
        (((self.0 / 1_000_000_000) / 100) % 100) as u32
    }

    pub fn seconds(&self) -> u32 {
        ((self.0 / 1_000_000_000) % 100) as u32
    }

    pub fn millis(&self) -> u32 {
        (self.0 % 1_000_000_000 / 1_000_000) as u32
    }

    pub fn micros(&self) -> u32 {
        (self.0 % 1_000_000_000 / 1_000) as u32
    }

    pub fn nanos(&self) -> u32 {
        (self.0 % 1_000_000_000) as u32
    }

    /// Returns the internal u64 representation of the time in nanosecond precision.
    ///
    /// # Examples
    /// ```
    /// # use qb_core::types::datetime::QBTime;
    /// let time = QBTime::new(2312).unwrap();          // HH:MM
    /// assert_eq!(time.as_u64(), 231200000000000);     // HHMMSSnnnnnnnnn
    /// ```
    pub fn as_u64(self) -> u64 {
        (self.hours() as u64 * 10000 + self.minutes() as u64 * 100 + self.seconds() as u64)
            * 1_000_000_000
            + self.nanos() as u64
    }

    /// Parse time from a string with a specific format
    ///
    /// Supported formats:
    /// - "%H" - Hours only
    /// - "%H:%M" - Hours and minutes
    /// - "%H:%M:%S" - Hours, minutes, and seconds
    /// - "%H:%M:%S.%3f" - Including milliseconds
    /// - "%H:%M:%S.%6f" - Including microseconds
    /// - "%H:%M:%S.%9f" - Including nanoseconds
    ///
    /// # Examples
    /// ```
    /// # use qb_core::types::datetime::QBTime;
    /// let time = QBTime::parse("23:59:59.123", "%H:%M:%S.%3f").unwrap();
    /// ```
    pub fn parse(time_str: &str, format: &str) -> QBResult<Self> {
        use chrono::NaiveTime;

        NaiveTime::parse_from_str(time_str, format)
            .map_err(|_| QBError::DateError {
                kind: DateErrorKind::ParseError,
                details: format!("Failed to parse '{}' with format '{}'", time_str, format),
            })
            .and_then(|t| {
                let hour = t.hour();
                let minute = t.minute();
                let second = t.second();
                let nano = t.nanosecond();

                if nano == 0 {
                    QBTime::from_u64(hour as u64 * 10000 + minute as u64 * 100 + second as u64)
                } else if nano % 1_000_000 == 0 {
                    QBTime::from_u64(
                        (hour as u64 * 10000 + minute as u64 * 100 + second as u64) * 1000
                            + (nano / 1_000_000) as u64,
                    )
                } else if nano % 1_000 == 0 {
                    QBTime::from_u64(
                        (hour as u64 * 10000 + minute as u64 * 100 + second as u64) * 1_000_000
                            + (nano / 1_000) as u64,
                    )
                } else {
                    QBTime::from_u64(
                        (hour as u64 * 10000 + minute as u64 * 100 + second as u64) * 1_000_000_000
                            + nano as u64,
                    )
                }
            })
    }
}

impl std::fmt::Display for QBDate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{:04}-{:02}-{:02}",
            self.year(),
            self.month(),
            self.day()
        )
    }
}

impl std::fmt::Display for QBTime {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let nanos = self.nanos();
        if nanos == 0 {
            write!(
                f,
                "{:02}:{:02}:{:02}",
                self.hours(),
                self.minutes(),
                self.seconds()
            )
        } else if nanos % 1_000_000 == 0 {
            write!(
                f,
                "{:02}:{:02}:{:02}.{:03}",
                self.hours(),
                self.minutes(),
                self.seconds(),
                self.millis()
            )
        } else if nanos % 1_000 == 0 {
            write!(
                f,
                "{:02}:{:02}:{:02}.{:06}",
                self.hours(),
                self.minutes(),
                self.seconds(),
                self.micros()
            )
        } else {
            write!(
                f,
                "{:02}:{:02}:{:02}.{:09}",
                self.hours(),
                self.minutes(),
                self.seconds(),
                nanos
            )
        }
    }
}

impl IntoQBDate for u32 {
    fn into_qbdate(self) -> QBResult<QBDate> {
        QBDate::from_u32(self)
    }
}

impl IntoQBDate for i32 {
    fn into_qbdate(self) -> QBResult<QBDate> {
        if self < 0 {
            return Err(QBError::DateError {
                kind: DateErrorKind::Invalid,
                details: format!("Invalid date {self}"),
            });
        }
        QBDate::from_u32(self as u32)
    }
}

impl IntoQBDate for u64 {
    fn into_qbdate(self) -> QBResult<QBDate> {
        if self > u32::MAX as u64 {
            return Err(QBError::DateError {
                kind: DateErrorKind::ParseError,
                details: format!("Failed to parse {self} into QBDate"),
            });
        }
        QBDate::from_u32(self as u32)
    }
}

impl IntoQBDate for i64 {
    fn into_qbdate(self) -> QBResult<QBDate> {
        if self > u32::MAX as i64 {
            return Err(QBError::DateError {
                kind: DateErrorKind::ParseError,
                details: format!("Failed to parse {self} into QBDate"),
            });
        }
        if self < 0 {
            return Err(QBError::DateError {
                kind: DateErrorKind::Invalid,
                details: format!("Invalid date {self}"),
            });
        }
        QBDate::from_u32(self as u32)
    }
}

impl IntoQBDate for String {
    fn into_qbdate(self) -> QBResult<QBDate> {
        let date =
            self.as_str()
                .replace("-", "")
                .parse::<u32>()
                .map_err(|_| QBError::DateError {
                    kind: DateErrorKind::ParseError,
                    details: format!("Failed to parse {self} into QBDate"),
                })?;
        QBDate::from_u32(date)
    }
}

impl IntoQBDate for &str {
    fn into_qbdate(self) -> QBResult<QBDate> {
        let date = self
            .replace("-", "")
            .parse::<u32>()
            .map_err(|_| QBError::DateError {
                kind: DateErrorKind::ParseError,
                details: format!("Failed to parse {self} into QBDate"),
            })?;
        QBDate::from_u32(date)
    }
}

impl IntoQBDate for Cow<'_, str> {
    fn into_qbdate(self) -> QBResult<QBDate> {
        let date =
            self.as_ref()
                .replace("-", "")
                .parse::<u32>()
                .map_err(|_| QBError::DateError {
                    kind: DateErrorKind::ParseError,
                    details: format!("Failed to parse {self} into QBDate"),
                })?;
        QBDate::from_u32(date)
    }
}

impl IntoQBDate for NaiveDate {
    fn into_qbdate(self) -> QBResult<QBDate> {
        let year = self.year();
        if year < 1900 || year > 3000 {
            return Err(QBError::DateError {
                kind: DateErrorKind::OutofRange,
                details: format!("Only support year between 1900 to 3000"),
            });
        }
        let month = self.month();
        let day = self.day();
        let date = (year as u32) * 10000 + month * 100 + day;
        QBDate::from_u32_unchecked(date)
    }
}

impl IntoQBDate for QBDate {
    fn into_qbdate(self) -> QBResult<QBDate> {
        Ok(self)
    }
}

/// Global trading calendar instance
static TRADING_CALENDAR: OnceLock<TradingCalendar> = OnceLock::new();

/// Trading calendar that manages trading dates for different exchanges
#[derive(Debug)]
pub struct TradingCalendar {
    /// Trading dates for each exchange, stored as a map of exchange code to a set of dates
    trading_dates: HashMap<String, Vec<QBDate>>,
}

impl TradingCalendar {
    /// Initialize the trading calendar from a TOML configuration file
    pub fn init(config_path: &str) -> QBResult<()> {
        if TRADING_CALENDAR.get().is_some() {
            return Ok(());
        }

        let content = fs::read_to_string(config_path).map_err(|e| QBError::DateError {
            kind: DateErrorKind::ParseError,
            details: format!("Failed to read calendar config: {}", e),
        })?;

        let config: Value = toml::from_str(&content).map_err(|e| QBError::DateError {
            kind: DateErrorKind::ParseError,
            details: format!("Failed to parse calendar config: {}", e),
        })?;

        let mut calendar = TradingCalendar {
            trading_dates: HashMap::new(),
        };

        if let Some(dates) = config.get("trade_dates").and_then(|v| v.as_table()) {
            for (exchange, dates) in dates {
                if let Some(dates) = dates.as_array() {
                    let dates: Vec<QBDate> = dates
                        .iter()
                        .filter_map(|d| d.as_integer().and_then(|s| s.into_qbdate().ok()))
                        .collect();
                    calendar.trading_dates.insert(exchange.clone(), dates);
                }
            }
        }

        TRADING_CALENDAR
            .set(calendar)
            .map_err(|_| QBError::DateError {
                kind: DateErrorKind::ParseError,
                details: format!("Failed to set global trading calendar"),
            })?;

        Ok(())
    }

    /// Get the global trading calendar instance
    pub fn instance() -> Option<&'static TradingCalendar> {
        TRADING_CALENDAR.get()
    }

    /// Check if a given date is a trading day for the specified exchange
    pub fn is_trading_day(&self, exchange: &str, date: QBDate) -> bool {
        self.trading_dates
            .get(exchange)
            .map(|dates| dates.binary_search(&date).is_ok())
            .unwrap_or(false)
    }

    /// Find the nearest trading day for the specified exchange and date
    /// If the date is already a trading day, returns the same date
    /// If search_next is true, finds the next trading day; otherwise finds the previous trading day
    pub fn nearest_trading_day(
        &self,
        exchange: &str,
        date: QBDate,
        search_next: bool,
    ) -> Option<QBDate> {
        if let Some(dates) = self.trading_dates.get(exchange) {
            match dates.binary_search(&date) {
                Ok(_) => Some(date),
                Err(idx) => {
                    if search_next {
                        dates.get(idx).copied()
                    } else {
                        if idx > 0 {
                            dates.get(idx - 1).copied()
                        } else {
                            None
                        }
                    }
                }
            }
        } else {
            None
        }
    }

    pub fn nearest_trading_day_opts(
        &self,
        exchange: &str,
        date: QBDate,
        opts: SearchOpts,
    ) -> Option<QBDate> {
        // 如果包含当前日期，直接使用现有的 nearest_trading_day
        if opts.include {
            return self.nearest_trading_day(exchange, date, opts.search_next);
        }

        let dates = self.trading_dates.get(exchange)?;

        match dates.binary_search(&date) {
            Ok(idx) => {
                if opts.search_next {
                    // 向后搜索：获取下一个交易日
                    dates.get(idx + 1).copied()
                } else {
                    // 向前搜索：获取前一个交易日
                    if idx > 0 {
                        dates.get(idx - 1).copied()
                    } else {
                        None
                    }
                }
            }
            Err(idx) => {
                if opts.search_next {
                    // 向后搜索：获取插入位置的日期
                    dates.get(idx).copied()
                } else {
                    // 向前搜索：获取插入位置前一个日期
                    if idx > 0 {
                        dates.get(idx - 1).copied()
                    } else {
                        None
                    }
                }
            }
        }
    }
}

pub struct SearchOpts {
    include: bool,
    search_next: bool,
}

pub fn get_days_in_month(year: u32, month: u32) -> u32 {
    match month {
        4 | 6 | 9 | 11 => 30,
        2 => {
            if is_leap_year(year) {
                29
            } else {
                28
            }
        }
        _ => 31,
    }
}

pub fn is_leap_year(year: u32) -> bool {
    (year % 4 == 0 && year % 100 != 0) || year % 400 == 0
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_qbdate_creation() {
        // Test valid dates
        assert!(QBDate::from_u32(20230101).is_ok());
        assert!(QBDate::from_u32(20231231).is_ok());
        assert!(QBDate::from_u32(20240229).is_ok()); // leap year

        // Test invalid dates
        assert!(QBDate::from_u32(18991231).is_err()); // year < 1900
        assert!(QBDate::from_u32(30010101).is_err()); // year > 3000
        assert!(QBDate::from_u32(20231232).is_err()); // invalid day
        assert!(QBDate::from_u32(20231301).is_err()); // invalid month
        assert!(QBDate::from_u32(20230229).is_err()); // not a leap year
    }

    #[test]
    fn test_date_components() {
        let date = QBDate::from_u32(20230415).unwrap();
        assert_eq!(date.year(), 2023);
        assert_eq!(date.month(), 4);
        assert_eq!(date.day(), 15);
    }

    #[test]
    fn test_date_comparison() {
        let date1 = QBDate::from_u32(20230101).unwrap();
        let date2 = QBDate::from_u32(20230102).unwrap();
        let date3 = QBDate::from_u32(20230101).unwrap();

        assert!(date1 < date2);
        assert!(date2 > date1);
        assert_eq!(date1, date3);
    }

    #[test]
    fn test_date_arithmetic() {
        let date = QBDate::from_u32(20230101).unwrap();

        // Test add_days
        let next_day = date.add_days(1).unwrap();
        assert_eq!(next_day.as_u32(), 20230102);

        // Test month boundary
        let next_month = date.add_days(31).unwrap();
        assert_eq!(next_month.as_u32(), 20230201);

        // Test year boundary
        let next_year = date.add_days(365).unwrap();
        assert_eq!(next_year.as_u32(), 20240101);

        // Test sub_days
        let prev_day = date.sub_days(1).unwrap();
        assert_eq!(prev_day.as_u32(), 20221231);
    }

    #[test]
    fn test_date_range() {
        let start = QBDate::from_u32(20230101).unwrap();
        let end = QBDate::from_u32(20230105).unwrap();

        let range = QBDateRange::new(start, end).unwrap();
        let dates: Vec<QBDate> = range.collect();

        assert_eq!(dates.len(), 5);
        assert_eq!(dates[0].as_u32(), 20230101);
        assert_eq!(dates[4].as_u32(), 20230105);
    }

    #[test]
    fn test_string_conversion() {
        // Test string format YYYYMMDD
        assert!(QBDate::new("20230101").is_ok());
        assert!(QBDate::new("2023-01-01").is_ok());

        // Test invalid formats
        assert!(QBDate::new("2023/01/01").is_err());
        assert!(QBDate::new("01-01-2023").is_err());
        assert!(QBDate::new("not a date").is_err());
    }

    #[test]
    fn test_naive_date_conversion() {
        let naive_date = NaiveDate::from_ymd_opt(2023, 1, 1).unwrap();
        let qb_date = QBDate::from_naive_date(naive_date).unwrap();
        assert_eq!(qb_date.as_u32(), 20230101);

        let converted_back = qb_date.to_naive_date().unwrap();
        assert_eq!(converted_back, naive_date);
    }

    #[test]
    fn test_month_operations() {
        let date = QBDate::from_u32(20230131).unwrap();

        // Test add months
        let next_month = date.add_months(1).unwrap();
        assert_eq!(next_month.as_u32(), 20230228); // January 31 -> February 28

        // Test add months with leap year
        let date_2024 = QBDate::from_u32(20240131).unwrap();
        let next_month_2024 = date_2024.add_months(1).unwrap();
        assert_eq!(next_month_2024.as_u32(), 20240229); // January 31 -> February 29

        // Test sub months
        let prev_month = date.sub_months(1).unwrap();
        assert_eq!(prev_month.as_u32(), 20221231); // January 31 -> December 31
    }

    #[test]
    fn test_nearest_trading_day_opts() {
        let mut calendar = TradingCalendar {
            trading_dates: HashMap::new(),
        };
        let exchange = "SHSE";
        
        // 使用实际的交易日历数据（按升序排列）
        let trading_dates: Vec<QBDate> = vec![
            QBDate::from_u32(20240923).unwrap(),
            QBDate::from_u32(20240924).unwrap(),
            QBDate::from_u32(20240925).unwrap(),
            QBDate::from_u32(20240926).unwrap(),
            QBDate::from_u32(20240927).unwrap(),
            QBDate::from_u32(20240930).unwrap(),
        ];
        calendar.trading_dates.insert(exchange.to_string(), trading_dates);

        // Case 1: 测试 include = true 的情况（当前日期是交易日）
        let opts = SearchOpts {
            include: true,
            search_next: true,
        };
        assert_eq!(
            calendar.nearest_trading_day_opts(exchange, QBDate::from_u32(20240925).unwrap(), opts),
            Some(QBDate::from_u32(20240925).unwrap())
        );

        // Case 2: 测试非交易日，向前搜索（周末情况）
        let opts = SearchOpts {
            include: false,
            search_next: true,
        };
        assert_eq!(
            calendar.nearest_trading_day_opts(exchange, QBDate::from_u32(20240928).unwrap(), opts),
            Some(QBDate::from_u32(20240930).unwrap())
        );

        // Case 3: 测试非交易日，向后搜索（周末情况）
        let opts = SearchOpts {
            include: false,
            search_next: false,
        };
        assert_eq!(
            calendar.nearest_trading_day_opts(exchange, QBDate::from_u32(20240928).unwrap(), opts),
            Some(QBDate::from_u32(20240927).unwrap())
        );

        // Case 4: 测试交易日，不包含当前日期，向前搜索
        let opts = SearchOpts {
            include: false,
            search_next: true,
        };
        assert_eq!(
            calendar.nearest_trading_day_opts(exchange, QBDate::from_u32(20240925).unwrap(), opts),
            Some(QBDate::from_u32(20240926).unwrap())
        );

        // Case 5: 测试交易日，不包含当前日期，向后搜索
        let opts = SearchOpts {
            include: false,
            search_next: false,
        };
        assert_eq!(
            calendar.nearest_trading_day_opts(exchange, QBDate::from_u32(20240925).unwrap(), opts),
            Some(QBDate::from_u32(20240924).unwrap())
        );

        // Case 6: 测试边界情况 - 第一个交易日
        let opts = SearchOpts {
            include: false,
            search_next: false,
        };
        assert_eq!(
            calendar.nearest_trading_day_opts(exchange, QBDate::from_u32(20240923).unwrap(), opts),
            None
        );

        // Case 7: 测试边界情况 - 最后一个交易日
        let opts = SearchOpts {
            include: false,
            search_next: true,
        };
        assert_eq!(
            calendar.nearest_trading_day_opts(exchange, QBDate::from_u32(20240930).unwrap(), opts),
            None
        );

        // Case 8: 测试无效交易所
        let opts = SearchOpts {
            include: false,
            search_next: true,
        };
        assert_eq!(
            calendar.nearest_trading_day_opts("INVALID", QBDate::from_u32(20240925).unwrap(), opts),
            None
        );
    }
}
