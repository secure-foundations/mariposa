# def add_query_option(parser):
#     parser.add_argument("-q", "--query", required=True, help="the input query")

def add_input_query_option(parser):
    parser.add_argument("-i", "--input-query-path", required=True, help="the input query")

def add_output_query_option(parser):
    parser.add_argument("-o", "--output-query-path", required=True, help="the query path")

def add_output_log_option(parser):
    parser.add_argument("--output-log-path", required=True, help="the query path")

def add_solver_option(parser):
    parser.add_argument("-s", "--solver", default="z3_4_12_2", help="the solver name (from solvers.json) to use")

def add_experiment_option(parser):
    parser.add_argument("-e", "--experiment", required=True, help="the experiment configuration name (from exps.json)")

def add_project_option(parser):
    parser.add_argument("-p", "--project", required=True, help="the project name under data/projects/")
    # parser.add_argument("--qtype", default=QueryType.ORIG, help="the project type under the project subroot")
    parser.add_argument("--part", default="1/1", help="which part of the project to run mariposa on (probably should not be specified manually)")

def add_clear_option(parser):
    parser.add_argument("--clear", default=False, action='store_true', help="clear the existing experiment directory and database")

def add_analyzer_option(parser):
    parser.add_argument("--analyzer", default="default", help="the analyzer name (from configs.json) to use")
    
def add_authkey_option(parser):
    parser.add_argument("--authkey", required=True, help="the authkey to use for the server pool")
