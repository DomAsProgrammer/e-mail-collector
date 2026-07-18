#!/usr/bin/env perl

=begin MetaInformation

	M E T A

	License:		GPLv3 - see license file or http://www.gnu.org/licenses/gpl.html
	Program-version:	0.1, (18th July 2026)
	Description:		Collects e-mails from a directory, merges them
				and sends them to a given address, and then archives them.
	Contact:		Dominik Bernhardt - domasprogrammer@gmail.com or https://github.com/DomAsProgrammer

=end MetaInformation

=begin License

	L I C E N S E

	DESCRIPTION
	Backup system basically using rsync and checking via find and du.
	Copyright (C) 2023  Dominik Bernhardt

	This program is free software: you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation, either version 3 of the License, or
	(at your option) any later version.

	This program is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with this program.  If not, see <https://www.gnu.org/licenses/>.

=end License

=begin VersionHistory

=end VersionHistory

=begin comment

	V A R I A B L E  N A M I N G

	str	string
	 L sql	sql code
	 L spf	sprintf() body.
	 L sha  Sha sum value
	 L cmd	command string
	 L ver	version number
	 L bin	binary data, also base64
	 L hex  hex coded data
	 L uri	path or url

	int	integer number
	 L cnt	counter
	 L pid	process id number
	 L tsp	seconds since period

	flt	floating point number

	bol	boolean

	mxd	unkown data (mixed)

	lop	loop header

	ref	reference
	 L rxp	regular expression
	 L are	array reference
	 L dsc	file discriptor (type glob)
	 L sub	anonymous subfunction	- DO NO LONGER USE, since Perl v5.26 functions can be declared lexically non-anonymous!
	 L cst	constant
	 L har	hash array reference
	  L obj  object (very often)
	  L tbl  table (a hash array with PK as key OR a multidimensional array AND hash arrays as values)
	   L csh  a table from or for e.g. a database or REST API table, but cashed within Perl

	Using prefixes in caps means constants.

=end comment

=cut


##### L I B R A R I E S #####
### Default
use strict;
use warnings;
use feature qw( try unicode_strings current_sub fc );
use builtin qw( true false );
no feature qw( bareword_filehandles );
use utf8;
use Time::Piece;
use File::Basename;
use Cwd qw( realpath );
## optionally
use Sys::Syslog qw( :standard :macros );	# writes to messages/journalctl
use Sys::Hostname;
use Getopt::Long qw( :config no_ignore_case bundling );
use File::Path qw( make_path );
use File::Copy;
use File::Find;
# MetaCPAN
use Email::MIME;

##### D E C L A R A T I O N #####

### Defaults
my ($strAppName, $uriAppPath)		= fileparse(realpath($0), qr/\.[^.]+$/);
my $verAppVersion			= q{1};
my $fltMinPerlVersion			= q{5.040000};		# $] but needs to be stringified!
my $strMinPerlVersion			= q{v5.40.0};		# $^V - nicer to read
my $pidParent				= $$;
my $objLock				= undef;
my @strBackupARGV			= @ARGV;

### System
#$|					= 1; # slurp mode
$ENV{LANG}				= q{C.UTF-8};
$ENV{LANGUAGE}				= q{C.UTF-8};
$ENV{LC_CTYPE}				= q{C.UTF-8};
$ENV{LC_ALL}				= undef;

### Getopt::Long
my $intLogLevel				= 4;
my $bolHelp				= false;
my $uriDirArchive			= undef;
my $uriDirMbox				= undef;
my $strEmail				= undef;
my $strFrom				= undef;
my $objTimeSent				= undef;
my $uriBinMail				= undef;

# Thresholds
my $intSizeHard				= 15 * 1024 ** 2;	# 15 MiB
my $intSizeNotice			=  9 * 1024 ** 2;	#  9 MiB

# Regular Expressions
my $rxpFrom				= qr{^From:?\s+(.+)$};
my $rxpTo				= qr{^To:?\s+(.+)$};
my $rxpSubject				= qr{^Subject:?\s+(.+)$};
my $rxpDate				= qr{^Date:?\s+(.+)$};
my $rxpEmptyLine			= qr{^\s*$};
my $rxpDotElement			= qr{^\..*$};
my $rxpValidComplexEmail		= qr{^(?:[a-z0-9!#$%&'*+\x2f=?^_`\x7b-\x7d~\x2d]+(?:\.[a-z0-9!#$%&'*+\x2f=?^_`\x7b-\x7d~\x2d]+)*|"(?:[\x01-\x08\x0b\x0c\x0e-\x1f\x21\x23-\x5b\x5d-\x7f]|\\[\x01-\x09\x0b\x0c\x0e-\x7f])*")@(?:(?:[a-z0-9](?:[a-z0-9\x2d]*[a-z0-9])?\.)+[a-z0-9](?:[a-z0-9\x2d]*[a-z0-9])?|\[(?:(?:(2(5[0-5]|[0-4][0-9])|1[0-9][0-9]|[1-9]?[0-9]))\.){3}(?:(2(5[0-5]|[0-4][0-9])|1[0-9][0-9]|[1-9]?[0-9])|[a-z0-9\x2d]*[a-z0-9]:(?:[\x01-\x08\x0b\x0c\x0e-\x1f\x21-\x5a\x53-\x7f]|\\[\x01-\x09\x0b\x0c\x0e-\x7f])+)\])$};
my $rxpValidEmail			= qr{^.+(?:@(?:.+\.[^.]{2,}|[0-9.:]{7,}))?$};

# Data
my $strDrawCharSplitHorizontal		= q{═};
my $areMails				= undef;
# $areMails	= [
	# {
		# uriFile		=> <URI to file>,
		# objContent		=> <OBJ Email::Simple>,	# NULL if email was not RFC2822 conform.
			# {
				# strFrom	=> <STR From address header>,
				# strTo	=> <STR To address header>,
				# strSubject	=> <STR Subject header>,
				# strDate	=> <STR Date header>,
				# strBody	=> <STR e-mail body>,
				# }
		# strRawContent		=> <STR file content>,	# Fallback if email was not RFC2822 conform.
		# intSizeFile		=> <INT bytes>,
		# tspMtime		=> <TSP modify time>,
		# },
	# ];


##### F U N C T I O N S #####
sub SetLogLevel () {
	my @cstLevels		= (
		LOG_EMERG,
		LOG_ALERT,
		LOG_CRIT,
		LOG_ERR,
		LOG_WARNING,
		LOG_NOTICE,	# Debug?
		LOG_INFO,
		LOG_DEBUG
		);

	setlogmask(LOG_UPTO( $cstLevels[$intLogLevel] // $cstLevels[-1] ));

	if ( IsDebug() ) {
		require Data::Dumper;
		Data::Dumper->import();
		}

	return(true);
	}

sub IsDebug () {
	if ( $intLogLevel >= 5 ) {
		return(true);
		}
	else {
		return(false);
		}
	}

sub Usage {
	my $intCodeReturn	= shift;
	my $dscSTD		= *STDOUT;

	if ( $intCodeReturn ) {
		$dscSTD		= *STDERR;
		}

	print $dscSTD qq{
Usage: $0 \\
  -m \$HOME/mbox \\
  -e example\@external.net \\
  -a \$HOME/mailArchive \\
  -M /usr/bin/mail \\
  -llllllll \\
  --help

  -m | --mbox-directory         - directory where Postfix' Maildir skeleton is
                                  expected and e-mails are collected from
  -e | --email-address          - e-mail address to send collected e-mails to
  -a | --archive-directory      - directory processed e-mails get stored
  -l | --loglevel               - stackable, defaults to -llll (LOG_WARNING, see
                                  syslog(3) for details)
  -s | --sendmail-binary        - optional: set path to Postfix' sendmail
                                  binary; searches in \$PATH by default
  -f | --from-address           - optional: set a sender's e-mail address;
                                  defaults to the currents user's name like from
                                  whoami(1)
  -h | --help                   - optional: shows this output
};

	exit($intCodeReturn);
	}

sub CheckEnvironment {
	my $bolErrors			= false;
	my $intErrorReturnCode		= 40;
	my @strMessageError		= ();

	syslog(LOG_DEBUG, q{%s}, q{CheckEnvironment: starting. Errors will be printed at the very end of this function.});

	syslog(LOG_DEBUG, q{CheckEnvironment: checking Perl version %s >= %s.}, $], $fltMinPerlVersion);
	if ( qq{$]} < $fltMinPerlVersion ) {
		$bolErrors		= true;

		push(@strMessageError, qq{Perl $^V is insufficient. You need at least Perl $strMinPerlVersion to run $strAppName!});
		}

	# Check given Getopts values
	## Archive Directory
	syslog(LOG_DEBUG, q{%s}, q{CheckEnvironment: checking archive target beeing a writable directory.});
	if ( ! defined($uriDirArchive) ) {
		$bolErrors		= true;
		$intErrorReturnCode	+= 1;
		
		push(@strMessageError, qq{Missing --archive-dir <dir>!});
		}
	elsif ( -e $uriDirArchive
	&& ! -d $uriDirArchive ) {
		$bolErrors		= true;
		$intErrorReturnCode	+= 1;
		
		push(@strMessageError, qq{Archive target "$uriDirArchive" is not a directory!});
		}
	elsif ( -d $uriDirArchive
	&& ! -w $uriDirArchive ) {
		$bolErrors		= true;
		$intErrorReturnCode	+= 1;
		
		push(@strMessageError, qq{Archive directory "$uriDirArchive" is not writable!});
		}

	# Mailbox folder checks
	syslog(LOG_DEBUG, q{%s}, q{CheckEnvironment: checking Maildir beeing a writable directory.});
	if ( ! defined($uriDirMbox) ) {
		$bolErrors		= true;
		$intErrorReturnCode	+= 2;
		
		push(@strMessageError, qq{Missing --mbox-dir <dir>!});
		}
	elsif ( -d $uriDirMbox
	&& -w $uriDirMbox ) {

		# Check if skeleton is as expected to verify Maildir directory
		if ( grep { ! -d qq{$uriDirMbox/$_} || ! -w qq{$uriDirMbox/$_} } qw( new cur tmp ) ) {
			$bolErrors		= true;
			$intErrorReturnCode	+= 2;

			push(@strMessageError, qq{No writable Maildir found. Make sure it was created before starting $strAppName and is writable to the effective user!});
			}
		}
	else {
		$bolErrors		= true;
		$intErrorReturnCode	+= 2;
		
		push(@strMessageError, qq{No writable Maildir found. Make sure it was created before starting $strAppName and is writable to the effective user!});
		}

	# E-mail address
	syslog(LOG_DEBUG, q{%s}, q{CheckEnvironment: checking e-mail address' validity.});
	if ( ! defined($strEmail) ) {
		$bolErrors		= true;
		$intErrorReturnCode	+= 4;
		
		push(@strMessageError, qq{Missing --email-address <example\@address.net>!});
		}
	elsif ( $strEmail !~ m{$rxpValidEmail}
	|| $strEmail !~ m{$rxpValidComplexEmail} ) {
		$bolErrors		= true;
		$intErrorReturnCode	+= 4;
		
		push(@strMessageError, qq{The e-mail address "$strEmail" is invalid!});
		}

	# From e-mail address
	syslog(LOG_DEBUG, q{%s}, q{CheckEnvironment: checking sender's e-mail address' validity.});
	if ( ! defined($strFrom) ) {
		$strFrom		= $ENV{LOGNAME} // $ENV{USER};
		$strFrom		.= q{@} . hostname();

		syslog(LOG_DEBUG, q{CheckEnvironment: set senders e-mail address to '%s'.}, $strFrom);
		}
	elsif ( $strFrom !~ m{$rxpValidEmail}
	|| $strFrom !~ m{$rxpValidComplexEmail} ) {
		$bolErrors		= true;
		$intErrorReturnCode	+= 8;
		
		push(@strMessageError, qq{The sender's e-mail address "$strEmail" is invalid!});
		}

	# Mail binary
	syslog(LOG_DEBUG, q{%s}, q{CheckEnvironment: checking sendmail binary.});
	if ( defined($uriBinMail) ) {
		syslog(LOG_DEBUG, q{CheckEnvironment: Got sendmail binary "%s".}, $uriBinMail);
		}
	else {
		chomp($uriBinMail	= qx(which sendmail));

		if ( $uriBinMail ) {
			syslog(LOG_DEBUG, q{CheckEnvironment: Found sendmail binary "%s".}, $uriBinMail);
			}
		else {
			$bolErrors		= true;
			$intErrorReturnCode	+= 16;

			push(@strMessageError, qq{Binary "sendmail" not found in \$PATH:$ENV{PATH}. Please supply manually!});
			}
		}

	# Final
	syslog(LOG_DEBUG, q{%s}, q{CheckEnvironment: showing errors if any.});
	if ( $bolErrors ) {
		my $strErrors		= join(qq{\n}, @strMessageError);

		print STDERR qq{\n$strErrors\n};
		syslog(LOG_ERR, qq{CheckEnvironment found errors:\n%s}, $strErrors);

		closelog();
		Usage($intErrorReturnCode);
		}

	return(true);
	}

sub CollectMails {
	my $strDirSource	= shift;
	my $intSizeSummary	= 0;
	my @harMails		= ();
	my sub findPreProc;
	my sub findWanted;
	my %mxdFindOptions	= (
		wanted		=> \&findWanted,
		preprocess	=> \&findPreProc,
		no_chdir	=> 1,
		);

	# Private functions
	sub findPreProc {
		grep { $_ !~ m{$rxpDotElement} } @_;
		}

	sub findWanted {
		if ( -f $File::Find::name ) {
			my %mxdMail	= (
				uriFile		=> $File::Find::name,
				objContent	=> undef,
				intSizeFile	=> ( stat($File::Find::name) )[7],
				tspMtime	=> ( stat(_) )[9],
				);

			push(@harMails, \%mxdMail);
			}
		}

	syslog(LOG_DEBUG, q{CollectMails: Searching e-mails in "%s".}, $strDirSource);

	find(\%mxdFindOptions, $strDirSource);

	syslog(LOG_DEBUG, q{%s}, q{CollectMails: Filtering e-mails.});

	# Sort by oldest first
	@harMails	= sort { $a->{tspMtime} <=> $b->{tspMtime} } @harMails;

	lopMailFilter:
	foreach my $mxdMail ( @harMails ) {
		if ( $mxdMail->{intSizeFile} >= $intSizeHard ) {
			my $strTextError	= qq{E-mail "$mxdMail->{uriFile}" is to huge, will be skipped.};

			print STDERR qq{$strTextError\n};
			syslog(LOG_ERR, q{%s}, $strTextError);

			next(lopMailFilter);
			}
		elsif ( $intSizeSummary + $mxdMail->{intSizeFile} >= $intSizeHard ) {
			my $strTextError	= qq{E-mail "$mxdMail->{uriFile}" is to huge to add to current mail, will be sent next time.};

			print STDERR qq{$strTextError\n};
			syslog(LOG_ERR, q{%s}, $strTextError);

			last(lopMailFilter);
			}

		syslog(LOG_DEBUG, q{Reading e-mail file "%s".}, $mxdMail->{uriFile});

		# Read e-mail
		if ( open(my $dscRead, q{<:encoding(UTF-8)}, $mxdMail->{uriFile}) ) {
			my $bolBody			= false;
			$mxdMail->{objContent}		= {
				strBody		=> '',
				};

			while ( my $strLine = readline($dscRead) ) {
				chomp($strLine);

				if ( $bolBody ) {
					$mxdMail->{objContent}{strBody}		.= qq{$strLine\n};
					}
				elsif ( $strLine =~ m{$rxpFrom} ) {
					$mxdMail->{objContent}{strFrom}		= $1;
					}
				elsif ( $strLine =~ m{$rxpTo} ) {
					$mxdMail->{objContent}{strTo}		= $1;
					}
				elsif ( $strLine =~ m{$rxpDate} ) {
					$mxdMail->{objContent}{strDate}		= $1;
					}
				elsif ( $strLine =~ m{$rxpSubject} ) {
					$mxdMail->{objContent}{strSubject}	= $1;
					}
				elsif ( $strLine =~ m{$rxpEmptyLine} ) {
					$bolBody	= true;
					}
				}
			
			close($dscRead);
			}
		else {
			my $strMessageError		= qq{Failed to read "$mxdMail->{uriFile}".};

			print STDERR qq{$strMessageError\n};
			syslog(LOG_ERR, q{%s}, $strMessageError);

			return(undef);
			}

		if ( $intSizeSummary >= $intSizeNotice ) {
			syslog(LOG_DEBUG, q{%s}, q{Threshold reached, no more messages are taken in account yet.});

			last(lopMailFilter);
			}
		}

	syslog(LOG_NOTICE, q{Loaded %d e-mails of the size of %.2f KiB.}, scalar(@harMails), $intSizeSummary / 1024);

	if ( IsDebug ) {
		syslog(LOG_DEBUG, qq{Mails read:\n%s\nRead done.}, Dumper({harMails => \@harMails}));
		}

	return(\@harMails);
	}

sub MergeMails {
	my $areMessages		= shift;
	my $intLogCounter	= 0;
	my @strMergedBody	= (
		sprintf(qq{The following %d e-mails were collected since the last run on %s.\n}, scalar(@{$areMessages}), hostname()),
		);

	syslog(LOG_DEBUG, qq{MergeMails: got %d e-mails to merge.}, scalar(@{$areMessages}));

	foreach my $mxdMail ( @{$areMessages} ) {

		syslog(LOG_DEBUG, q{MergeMails: merging mail %} . length(scalar(@{$areMessages})) .q{s/%d "%s".},
			++$intLogCounter,
			scalar(@{$areMessages}), 
			$mxdMail->{uriFile},
			);

		push(@strMergedBody, sprintf(qq{\n%s\n}, $strDrawCharSplitHorizontal x 77));

		if ( defined($mxdMail->{objContent}) ) {
			push(@strMergedBody,
				sprintf(qq{   From : %s\n     To : %s\n   Date : %s\nSubject : %s\n\n%s\n},
					$mxdMail->{objContent}{strFrom},
					$mxdMail->{objContent}{strTo},
					$mxdMail->{objContent}{strDate},
					$mxdMail->{objContent}{strSubject},
					$mxdMail->{objContent}{strBody},
					)
				);
			}
		else {
			push(@strMergedBody, sprintf(qq{\n%s\n}, $mxdMail->{strRawContent}));
			}
		}

	syslog(LOG_DEBUG, qq{Merge done:\n%s\n<End of message>}, join('', @strMergedBody));

	return(join('', @strMergedBody));
	}

sub SendMails {
	my $strAddressTo	= shift;
	my $strAddressFrom	= shift;
	my $strMessage		= shift;
	my $uriBinary		= shift;
	my $objTimeSent		= undef;
	my $objMimeEmail	= undef;
	my @strArgs		= (
		$uriBinary,
		q{-t},
		q{-oi},
		);

	syslog(LOG_DEBUG, q{%s}, q{SendMails: Generating MIME message.});

	$objMimeEmail		= Email::MIME->create(
		header_str => [
			From    => $strAddressFrom,
			To      => $strAddressTo,
			Subject => q{Collected Mails from the Milkyway},
			],

		attributes => {
			content_type => 'text/plain',
			charset      => 'UTF-8',
			encoding     => 'base64',
			},

		body_str => $strMessage,
		);

	if ( IsDebug ) {
		syslog(LOG_DEBUG, qq{New email:\n%s}, Dumper({objMimeEmail => $objMimeEmail, Message => do { $objMimeEmail->as_string },}));
		}

	syslog(LOG_INFO, q{SendMails: sending e-mail from %s to %s using %s.}, $strAddressFrom, $strAddressTo, $uriBinary);

	if ( open(my $dscPH, q{|-:encoding(UTF-8)}, @strArgs) ) {
		print $dscPH $objMimeEmail->as_string;
		close($dscPH);

		$objTimeSent	= localtime;
		}
	else {
		syslog(LOG_ERR, q{%s}, q{Failed to send e-mail.});
		
		return(undef);
		};

	syslog(LOG_DEBUG, q{%s}, q{E-mail sent.});

	return($objTimeSent);
	}

sub ArchiveMails {
	my $uriDirFinal		= shift;
	my $objTimeSent		= shift;
	my $areMsgs		= shift;
	my @uriFiles		= map { $_->{uriFile} } @{$areMsgs};

	syslog(LOG_DEBUG, q{%s}, q{ArchiveMails: calculating final directory.});

	$uriDirFinal		= sprintf(q{%s/%s%+03d:%02d},
		$uriDirFinal,
		$objTimeSent->datetime,
		$objTimeSent->tzoffset->hours,
		$objTimeSent->tzoffset->minutes % 60,
		);

	syslog(LOG_DEBUG, qq{ArchiveMails: going to archive the following list to "%s":\n%s},
		$uriDirFinal,
		join(qq{\n}, @uriFiles));

	make_path($uriDirFinal);

	foreach my $uriSource ( @uriFiles ) {
		move($uriSource, $uriDirFinal) or
		syslog(LOG_ERR, q{Failed to move "%s" to "%s".}, $uriSource, $uriDirFinal);
		}

	syslog(LOG_DEBUG, q{%s}, q{E-mails archived.});

	return(\@uriFiles);
	}


##### M A I N #####
openlog($strAppName, q{pid}, LOG_MAIL);

GetOptions(
	q{l|loglevel+}			=> \$intLogLevel,
	q{a|archive-directory=s}	=> \$uriDirArchive,
	q{m|mbox-directory=s}		=> \$uriDirMbox,
	q{e|email-address=s}		=> \$strEmail,
	q{s|sendmail-binary=s}		=> \$uriBinMail,
	q{f|from-address=s}		=> \$strFrom,
	q{h|help}			=> \$bolHelp,
	) or Usage(1);

if ( $bolHelp ) {
	Usage(0);
	}

SetLogLevel();
syslog(LOG_DEBUG, q{%s}, qq{Supplied parameters:\n  $0 @strBackupARGV});

# Arguments are the option list of GetOptions() - will exit itself
CheckEnvironment();

$areMails = CollectMails($uriDirMbox);
if ( ! defined($areMails)
|| ref($areMails) ne q{ARRAY} ) {
	closelog();
	exit(4);
	}
elsif ( @{$areMails} ) {
	my $strNewBody	= undef;

	$strNewBody = MergeMails($areMails);
	if ( ! $strNewBody ) {
		closelog();
		exit(1);
		}

	$objTimeSent	= SendMails($strEmail, $strFrom, $strNewBody, $uriBinMail);
	if ( ! $objTimeSent ) {
		closelog();
		exit(2);
		}

	if ( ! ArchiveMails($uriDirArchive, $objTimeSent, $areMails) ) {
		closelog();
		exit(3);
		}
	}

closelog();
exit(0);
__DATA__
