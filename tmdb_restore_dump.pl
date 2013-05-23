#!/usr/bin/env perl
#########################
# bugfix: 解决 打开文件失败也返回 0 的情况
# Author: billyxue
# Email: crakcer0@126.com

###################
# example:
#restore all db in current dir  or sep dir
# *  perl tmdb_restore_dump.pl --all-databases --backupset-dir='192.168.2.10'
# *	perl tmdb_restore_dump.pl --all-databases --backupset-dir='192.168.2.10','192.168.2.11'

#restore sep db name in current dir  or sep dir
# *	perl tmdb_restore_dump.pl --backupset-dir='192.168.2.10','192.168.2.11' --databases=PP_50,PP_79

#restore sep db name + table_reg  in current dir  or sep dir
# * perl tmdb_restore_dump.pl --backupset-dir='192.168.2.10','192.168.2.11' --databases=PP_50,PP_79  --tables-file=./table_list 
# 
# t_paipai_[0-9][0-9]
# t_pp_pet_[00-99][00-99]

# perl tmdb_restore_dump.pl --backupset-dir='192.168.2.10','192.168.2.11' --databases=PP_50,PP_79  --tables-file=./table_list --user=root --password=admina

# TODO: 排除系统库 mysql的恢复
## A script for making resotre table data from mysqldump with gzip  like  xxx.gz
## 
#
# ------------- DIR ---------------
# ------------- 	Database(s) ---------------
# ------------- 		table(s) ---------------
# ----------------------------------------------
use warnings FATAL => 'all';
use strict;
use Getopt::Long;
use File::Spec;
use Pod::Usage qw(pod2usage);
use POSIX "strftime";
use POSIX ":sys_wait_h";
use IO::Prompt;
use FileHandle;
use File::Basename;
use File::Temp;
use File::Find;
use File::Copy;
use English qw(-no_match_vars);
use Time::HiRes qw(usleep);

use Data::Dumper;

my $program_name;

my $option_help='';
my $option_version='';

my $option_sleep;

my $option_backupet_dir;   # multi:  -d=dir1,dir2

my $option_databases;
my $option_tables_file;
my $option_all_databases='';   #can not be set with $option_tables_file both

my $option_mysql_socket;
my $option_mysql_user;
my $option_mysql_password;
my $option_mysql_port;
my $option_mysql_host;

my $option_tmpdir;
my $option_parallel;
my $default_parallel = 1;
my @chd_pids = ();

my $now='';
my %mysql;

my %table_list=();

my @table_name_reg = ();
my @table_name_bind = ();

my %database_bakset_ha=();
my @need_database_bakset_ha=();

my $mysql_keep_alive = 5;

my $tmdb_restore_version = '1.0';
my $copyright_notice =
"Taomee Database Restore Utility v${tmdb_restore_version}; 
 Copyright 2012, 2013 Taomee Oy All Rights Reserved.

This software is published under
the GNU GENERAL PUBLIC LICENSE Version 2, June 1991.

";

# check existence of DBD::mysql module
eval {
    require DBD::mysql;
};
my $dbd_mysql_installed = $EVAL_ERROR ? 0 : 1;

# force flush after every write and print
$| = 1;

$program_name = basename($0);

sub usage
{
	my $msg = shift || '';
	pod2usage({ -msg => $msg, -verbose => 1});
	return 0;
}

sub print_version 
{
    printf(STDERR $copyright_notice);
}

sub	parse_table_arg
{
	my ( $filename ) = @_;
	return unless $filename;

	open my $fh, '<', $filename   or die "can not open the file : $filename $!";
	if ( $fh ) {
		while ( my $line = <$fh> ) {
			chomp $line;
			#my ( $db, $tbl ) = $line =~ m/\s*([^\.]+)\.([^\.]+)\s*/;
			#$table_list{$db}->{$tbl} = 1;
			push @table_name_reg, $line;
		}
	}
}

sub check_dir_exists
{
	my $dir = shift;
	die "$dir is Not a directory" unless -d $dir;
	return 0;
}


sub collect_bak_sets
{
	my $d_ref = shift;
	for my $td (@{$d_ref})
	{
		print "DEBUG  start to check $td\n";
		my $ret;
		my @tfile=();
		$ret = check_dir_exists($td);
		if (! $ret) {
			opendir (THISD , "$td" ) or die "Can NOT open dir: $td  $!";
			while( my $file = readdir( THISD ) ) 
			{
				next if ( $file eq '.' || $file eq '..' );  
				my $db_match_reg = '[a-zA-Z0-9_]';
				if ($file =~ /($db_match_reg+)(.).*gz/ && -f "$td/$file")
				{
					#print "==db: $1  file: $file\n";
					if ( !exists $database_bakset_ha{$1} ) {
						$database_bakset_ha{$1} = "$td/$file";
					} else {
						die "There are more than 1 db named: $1 check\n";
					}
				}
			}
			#push @backup_set_file_name , grep {$_} (shift @tfile) while @tfile;
			closedir THISD;
		}
	}
}

sub file_to_array 
{
	my $filename = shift;
	my $lines_ref = shift;

	open(FILE, $filename) || die "can't open file '$filename': $!";
	@{$lines_ref} = <FILE>;
	close(FILE) || die "can't close file '$filename': $!";

	foreach my $a (@{$lines_ref}) {
		chomp($a);
	}
}

sub parse_database_arg
{
	my $item;
	if ($option_databases =~ /\// )
	{
		print "databaes is in a file\n";
		if (! -f $option_databases){
			die "but can not be read $!\n";
		}
		my @lines ;
		file_to_ary($option_databases, \@lines);
		$option_databases = join (" ", @lines);
	}

	foreach $item (split(/,/, $option_databases)) {
		my $db;
		my $table;
		next if $item eq ""; 
		if ( exists $database_bakset_ha{$item} )
		{
			print "need restore db: $item  file: $database_bakset_ha{$item}\n";
			push @need_database_bakset_ha, $database_bakset_ha{$item};
		}else {
			warn "****** No backupset restore for db:  $item ******\n";
		}
	}
}


sub quit 
{
	my %incoming = ();
	(
		$incoming{'message'},
		$incoming{'errorLevel'}
	) = @_;


	$incoming{'errorLevel'} = 0 if (!defined($incoming{'errorLevel'}));

	## Print exit message
	if ($incoming{'message'}) { 
		print($incoming{'message'});
	}

	## Exit
	exit($incoming{'errorLevel'});
}

sub get_current_time 
{
	return strftime("%y%m%d %H:%M:%S", localtime());
}

sub init_sig
{
  ## Set STDOUT to flush immediatly after each print  
  $| = 1;

  ## Intercept signals
  $SIG{'QUIT'}  = sub { quit("$$ - $program_name - EXITING: Received SIG$_[0]", 1); };
  $SIG{'HUP'}   = sub { quit("$$ - $program_name - EXITING: Received SIG$_[0]", 1); };
  $SIG{'INT'}   = sub { quit("$$ - $program_name - EXITING: Received SIG$_[0]", 1); };
  $SIG{'KILL'}  = sub { quit("$$ - $program_name - EXITING: Received SIG$_[0]", 1); };
  $SIG{'TERM'}  = sub { quit("$$ - $program_name - EXITING: Received SIG$_[0]", 1); };
  return(1);
}

sub check_args
{
	my $answer;
	my $ret;
	if (@ARGV == 0) {
		print STDERR "You will restore all \"\*.gz\" file in current directory.\n";
		$answer = prompt("continue [y/N]> ");
		if( $answer =~ /N/i){
			exit(1);
		}
	}

	$ret = GetOptions(
		'help'		=> \$option_help,
		'version'	=> \$option_version,
		'sleep=i' 	=> \$option_sleep,

		'backupset-dir=s' => \$option_backupet_dir,

		'all-databases'  => \$option_all_databases,
		'databases=s'    => \$option_databases,
		'tables-file=s', => \$option_tables_file,

		'user=s' 	=> \$option_mysql_user,
		'password:s'=> \$option_mysql_password,
		'host=s' 	=> \$option_mysql_host,
		'port=s' 	=> \$option_mysql_port,
		'socket=s' 	=> \$option_mysql_socket,

		'tmpdir=s' => \$option_tmpdir,

		'parallel=i' => \$option_parallel,
	);

	if (!$ret) {
		# failed to read options
		print STDERR "Bad command line arguments\n";
		exit(1);
	}

	if ($option_help) {
		usage();
		exit(0);
	}

	if ($option_version) {
		print_version();
		exit(0);
	}

	if ($option_all_databases && $option_databases) {
		print STDERR "--all-databases and --databases " .
		"options are mutually exclusive\n";
		exit(1);
	}

	if ($option_all_databases && $option_tables_file) {
		print STDERR "--all-databases and --tables-file " .
		"options are mutually exclusive\n";
		exit(1);
	}

}

sub init_global_var
{
	if (!$option_parallel)
	{
		$option_parallel  = $default_parallel;
	}

	print "$option_parallel\n";

	my @dirs;
	if ($option_backupet_dir){
		if ($option_backupet_dir =~ /,/){
			@dirs = split /,/, $option_backupet_dir;
		}else {
			push @dirs , $option_backupet_dir;
		}
	}else {
		$option_backupet_dir = ".";
		push @dirs , dirname($0);
	}

	print join " --- \n", @dirs,"\n";
	# acrroding the @dir collect  all  *.sql.gz  file

	collect_bak_sets(\@dirs);

	if ( scalar keys %database_bakset_ha == 0 )
	{
		die "no *.gz file found you may try sepcify the --backupset-dir\n";
	}

	# -- here wo go -- 
	if ($option_all_databases) {
		printf("Restore Level: All Databases\n");
		print join "\n", keys %database_bakset_ha,"\n";
	}elsif ($option_databases) {
		printf("Restore Level: Database\n");
		print "="x40,"\n";
		parse_database_arg();
	} 

	if ($option_tables_file) {
		printf("Restore Level: Table\n");
		print "="x40,"\n";
		parse_table_arg($option_tables_file);
	}
	print join "== ==\n", @table_name_reg, "\n";

}

sub parse_connection_options
{
	my $con = shift;
	$con->{dsn} = 'dbi:mysql:';

	if ($option_mysql_password) {
		$con->{dsn_password} = "$option_mysql_password";
	}
	if ($option_mysql_user) {
		$con->{dsn_user} = "$option_mysql_user";
	}
	if ($option_mysql_host) {
		$con->{dsn} .= ";host=$option_mysql_host";
	}
	if ($option_mysql_port) {
		$con->{dsn} .= ";port=$option_mysql_port";
	}
	if ($option_mysql_socket) {
		$con->{dsn} .= ";mysql_socket=$option_mysql_socket";
	}
}

#
# Start a background process that will send keep-alive queries periodically
# using the connection passed as a 'mysql' hash reference
#
sub start_keepalives 
{
	my $con = shift;

	if (defined($con->{keep_alive_pid})) {
		die "Keep-alive process has already been started for this connection."
	}

	my $keep_alive_pid = fork();

	if ($keep_alive_pid) {
		# parent process
		$con->{keep_alive_pid} = $keep_alive_pid;
		return;
	}

	# child process
	$con->{dbh}->{InactiveDestroy} = 1;

	my $rc = 0;
	my $hello_id = 0;

	# send dummy queries to connection until interrupted with SIGINT or a
	# connection error
	while (!$rc) {
		sleep $mysql_keep_alive;

		my $hello_message = "in restore ping " . $hello_id++;

		eval {
			$con->{dbh}->selectrow_array("select '$hello_message'");
		};

		if ($EVAL_ERROR) {
			$rc = 255;
		}
	}
	exit $rc;
}

sub mysql_connect 
{
	my %con;
	my %args = (
		abort_on_error => 1,
		keepalives => 0,
		@_
	);

	$con{abort_on_error} = $args{abort_on_error};
	$con{keepalives} = $args{keepalives};

	parse_connection_options(\%con);

	$now = get_current_time();
	print STDERR "$now  Connecting to MySQL server with DSN '$con{dsn}'" .
	(defined($con{dsn_user}) ? " as '$con{dsn_user}' " : "") .
	" (using password: ";

	if (defined($con{dsn_password})) {
		print STDERR "YES).\n";
	} else {
		print STDERR "NO).\n";
	}

	eval {
		$con{dbh}=DBI->connect($con{dsn}, $con{dsn_user},
			$con{dsn_password}, { RaiseError => 1 });
	};

	if ($EVAL_ERROR) {
		$con{connect_error}=$EVAL_ERROR;
	} else {
		$now = get_current_time();
		print STDERR "$now Connected to MySQL server\n";
	}

	if ($args{abort_on_error}) {
		if (!$dbd_mysql_installed) {
			die "ERROR: Failed to connect to MySQL server as " .
			"DBD::mysql module is not installed " .
			"Please contact sys admin: or apt-get install libdbd-mysql (Debian)";
		} else {
			if (!$con{dbh}) {
				die "ERROR: Failed to connect to MySQL server: " .
				$con{connect_error};
			}
		}
	}

	if ($con{dbh} && $con{keepalives}) {
		$con{dbh}->do("SET SESSION wait_timeout=2147483");
		start_keepalives(\%con);
	}

	return %con;
}

#
# Stop the background keep-alive process
#
sub stop_keepalives 
{
    my $con = shift;

    if (!defined($con->{keep_alive_pid})) {
        die "Keep-alive process has never been started for this connection."
    }

    kill 'INT', $con->{keep_alive_pid};
    waitpid($con->{keep_alive_pid}, 0);
    my $rc = $? >> 8;

    if ($rc != 0) {
        die "Keep-alive process died with exit code " . $rc;
    }
    undef $con->{keep_alive_pid};
}


#
# mysql_close subroutine closes connection to MySQL server gracefully.
# 
sub mysql_close 
{
		my $con = shift;

		if ($con->{keepalives}) {
			stop_keepalives($con);
		};

		$con->{dbh}->disconnect();

		$now = get_current_time();
		print STDERR "$now  Connection to database server closed\n";
}

sub connect_db_spy
{
	%mysql = mysql_connect(
		abort_on_error => 1,
		keepalives => 0
	);
	if ($mysql{dbh}) {
		print STDERR "Connected successfully\n";
		mysql_close(\%mysql);
	} else {
		die "Can not connect  check your db options\n";
	}
}


#######################################################################
#  main start 
#######################################################################
init_sig();

#sleep(30);
check_args();

# initialize global variables and perform some checks
init_global_var();

# test if we can connect to mysql db
connect_db_spy();


######################## may need use perlipc
# 用一个hash标识哪个任务是完成的，不需要重做

our @IP = @need_database_bakset_ha;
our $TOTAL_TASK = @IP; 
our $MAX_LIVE_PROC = $option_parallel;
our $zombies = 0; 
$SIG{CHLD} = sub { $zombies++ }; # handle message from kernel 
print "total task:   $TOTAL_TASK\n";

our $handled_task = 1; 
our $cur_live_proc = 1; 

my %pid_job = ();
my %job_status = ();

sub init_job_status
{
	for my $k( 0 .. $TOTAL_TASK-1 )
	{
		$job_status{$k} = 'todo';
	}
}

init_job_status();

sub find_todo_job
{
	for my $k ( 0 .. $TOTAL_TASK -1 ) {
		if ( $job_status{$k} eq 'todo' 
		  || $job_status{$k} eq 'redo' ) 
	  {
		  return $k;
	  }
  }
  return -1;
}

my $job_idx = -1;

$job_idx = find_todo_job();
if ($job_idx != -1) {
	print "job index: ---- $job_idx ----\n";
	my $pid = fork; 
	unless ($pid) { 
		start_restore_work($IP[$job_idx]);
		exit 0; 
	}else {
		print "pid : $pid   job : $IP[$job_idx]\n";
		$pid_job{$pid} = $job_idx;
		print "op ----0---$job_idx ------\n";
		$job_status{$job_idx} = 'doing';
	}
}
else {
	print "Nothing todo\n";
}

while ($cur_live_proc>0) 
{ 
	if ($zombies>0) 
	{ 
		$zombies=0; 
		my $collect = 0; 
		while(($collect = waitpid(-1, WNOHANG)) > 0) 
		{ 
			$cur_live_proc--; 
			print "---- ret value: $?  collect value: $collect\n";
			if ( $? == 0 ) {
				#print "-------- 1   job status key: $pid_job{$collect}\n";
				$job_status{$pid_job{$collect}} = 'done';
			} else {
				#print "-------- 2 job status key: $pid_job{$collect}\n";
				$job_status{$pid_job{$collect}} = 'redo';
				$handled_task--; 
			}
		} 
	} 
	if ( ($cur_live_proc<$MAX_LIVE_PROC) and ($handled_task<$TOTAL_TASK) ) { 
		$handled_task++; 
		$cur_live_proc++; 

		$job_idx = find_todo_job();
		if ($job_idx != -1) {
			my $pid = fork(); 
			unless ($pid) { 
				start_restore_work($IP[$job_idx]);
				exit 0; 
			}else {
				#print "pid : $pid   job : $IP[$job_idx]\n";
				$pid_job{$pid} = $job_idx;
				$job_status{$job_idx} = 'doing';
			}
		}
	} else { 
		next; 
	} 
} 

print "\n";

print Dumper %job_status;
exit(0);

sub start_restore_work
{
	my $file = shift;
	print "start to restore file: $file \n";
	sleep(2);

=head
	if ($file =~ /PP_50/ || $file =~ /PP_79/ )
	{
		system("echo ok > pp50");
		# 成功 0
		# 失败 255
		exit(0);
	} 
	else 
	{
		system("echo failed > pp51");
		#exit(0);
		exit(255);
	}

=cut
	my $res_start_time = get_current_time();
	my $res_finish_time;

	my $rc = 0;
	if ( $file =~ /\.gz$/ ) {
		eval {
			open ( IN, "gunzip -c $file |") or die "can't open pipe to $file";
		};
	}
	else {
		eval { 
			open( IN, $file ) or die "can't open $file";
		};
	}

	if ($EVAL_ERROR) {
		$rc = 255;
		exit($rc);
	}else {
		exit(0);
	}

	my $curtab='';
	while (<IN>) 
	{
		if ($_ =~ /^-- Table structure for table `(.*)`/){
			$curtab = $1;
			foreach my $r (@table_name_reg) {
				if ($curtab =~ /$r/ ) {
					print "find $curtab\n";
				}
			}
		}
	}

	print "start to restore file: $file ok\n\n";
	exit(0);
}






=pod

=head1 NAME

tmdb_restore_dump - taomee dba restore tool for xxx.gz file (mysqldump + gzip)

=head1 SYNOPOSIS

tmdb_restore_dump [-] [--user=NAME]
	[--password=WORD] [--port=PORT] [--socket=SOCKET]


=head1 DESCRIPTION


The first command line above makes a hot backup of a MySQL database.
By default it creates a backup directory (named by the current date


=head1 OPTIONS

=over

=item --help

This option displays a help screen and exits.

=item --host=HOST

This option specifies the host to use when connecting to the database server with TCP/IP.  The option accepts a string argument. It is passed to the mysql child process without alteration. See mysql --help for details.

=item --password=WORD

This option specifies the password to use when connecting to the database. It accepts a string argument.  It is passed to the mysql child process without alteration. See mysql --help for details.

=item --port=PORT

This option specifies the port to use when connecting to the database server with TCP/IP.  The option accepts a string argument. It is passed to the mysql child process. It is passed to the mysql child process without alteration. See mysql --help for details.

=item --stream=STREAMNAME

This option specifies the format in which to do the streamed backup.  The option accepts a string argument. The backup will be done to STDOUT in the specified format. Currently, the only supported formats are tar and xbstream. This option is passed directly to xtrabackup's --stream option.

=item --tables-file=FILE

This option specifies the file in which there are a list of names of the form database.  The option accepts a string argument.table, one per line. The option is passed directly to xtrabackup's --tables-file option.

=item --version

This option displays the xtrabackup version and copyright notice and then exits.

=back

=head1 BUGS

Bugs can be reported on Launchpad: http://dbm.taomee.com
Author: billy@taomee.com

=head1 COPYRIGHT


This software is published under the GNU GENERAL PUBLIC LICENSE Version 2, June 1991.

=cut


