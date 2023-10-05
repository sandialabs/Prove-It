import sqlite3

class Database:
    '''
    The Database class uses sqlite3 to maintain a database of
    relations (tables) for a theory package.
    '''

    def __init__(self, directory, db_file_name, package_name):
        '''
        Initialize a database, creating a standard set of tables
        to hold common expressions, axioms, theorems, proof steps, etc.
        The database will be directory/db_file_name, where directory
        is an absolute path (currently provided in the __init__() for
        the TheoryStorage class), db_file_name is expected be a string
        of the form 'name.db', and package_name will typically be
        a string like 'proveit/logic/booleans/implication', specifying
        the theory package the database serves.
        Using directory = '' (i.e. an empty string) creates a db in
        whatever current folder the __init__() takes place from;
        in particular, use directory = '' to create a db in the
        current folder from which a Jupyter notebook is being run.

        Details involving foreign keys are still being worked out ---
        in particular, what happens when the source of a foreign key
        is deleted? For example, can we make use of automatic database
        processes to update/delete a judgment record if its underlying
        expression has been deleted from the expression table?

        The tables also do not yet implement any explicit "used by"
        attribute(s).

        The theorem table does not yet record whether or not the
        theorem is still a conjecture or has a conjecture-based proof
        or a non-conjecture-base proof. We might use an attribute
        such as 'proof_status' with possible values of 'conjecture',
        'conjecture-based', or 'complete'.

        # Recall that we have only five data types to work with:
        # NULL
        # INTEGER
        # REAL
        # TEXT
        # BLOB
        '''

        # Allow the directory to be empty, and if not empty then
        # with or without the ending forward slash '/'.
        if (directory != '' and directory[-1] != '/'):
            # augment directory name with a forward slash
            directory = directory + '/'
        self.file_name = db_file_name
        self.directory = directory
        self.pkg_name = package_name
        # for convenience:
        self.full_path_file_name = self.directory + self.file_name

        # connect to (or create) the database
        conn = sqlite3.connect(self.full_path_file_name)

        # create a cursor
        c = conn.cursor()

        # create our tables/relations,
        # deleting each first if it already exists
        # (The deletions will eventually be omitted, instead using
        # the following code:
        # c.execute("""CREATE TABLE IF NOT EXISTS table_name(...)""")

        # c.execute("""CREATE TABLE IF NOT EXISTS common (
        c.execute("DROP TABLE IF EXISTS common")
        c.execute("""CREATE TABLE common (
            id            TEXT NOT NULL PRIMARY KEY,
            path_name     TEXT,
            name          TEXT,
            expression    TEXT,
            string_format TEXT,
            latex_format  TEXT,
            FOREIGN KEY (expression) REFERENCES expression (id)
            )""")

        # Eventually the axiom table will be reduced to holding
        # just id and name (like the associated name_to_hash.txt files)
        # c.execute("""CREATE TABLE IF NOT EXISTS axiom (
        c.execute("DROP TABLE IF EXISTS axiom")
        c.execute("""CREATE TABLE axiom (
            id            TEXT NOT NULL PRIMARY KEY,
            path_name     TEXT,
            name          TEXT,
            judgment      TEXT,
            string_format TEXT,
            latex_format  TEXT
            )""")

        # c.execute("DROP TABLE IF EXISTS definition")
        # c.execute("""CREATE TABLE definition (
        c.execute("""CREATE TABLE IF NOT EXISTS definition (
            name       TEXT,
            expression TEXT
            )""")

        # c.execute("""CREATE TABLE IF NOT EXISTS theorem (
        c.execute("DROP TABLE IF EXISTS theorem")
        c.execute("""CREATE TABLE theorem (
            id            TEXT NOT NULL PRIMARY KEY,
            path_name     TEXT,
            name          TEXT,
            judgment      TEXT,
            string_format TEXT,
            latex_format  TEXT,
            FOREIGN KEY (judgment) REFERENCES judgment (id)
            )""")

        # c.execute("DROP TABLE IF EXISTS proof_step")
        # c.execute("""CREATE TABLE proof_step (
        c.execute("""CREATE TABLE IF NOT EXISTS proof_step (
            id                    TEXT NOT NULL PRIMARY KEY,
            type                  TEXT,
            path_name             TEXT,
            name                  TEXT,
            judgment              TEXT,
            requirements          TEXT,
            equality_requirements TEXT,
            instantiations        TEXT,
            string_format         TEXT,
            latex_format          TEXT,
            FOREIGN KEY (judgment) REFERENCES judgment (id)
            )""")

        # c.execute("DROP TABLE IF EXISTS judgment")
        # c.execute("""CREATE TABLE judgment (
        c.execute("""CREATE TABLE IF NOT EXISTS judgment (
            id            TEXT NOT NULL PRIMARY KEY,
            expression    TEXT NOT NULL,
            assumptions   TEXT,
            num_lit_gens  INTEGER,
            string_format TEXT,
            latex_format  TEXT,
            FOREIGN KEY (expression) REFERENCES expression (id)
            )""")

        # c.execute("DROP TABLE IF EXISTS expression")
        # c.execute("""CREATE TABLE expression (
        c.execute("""CREATE TABLE IF NOT EXISTS expression (
            id             TEXT NOT NULL PRIMARY KEY,
            subexpressions TEXT,
            class_path     TEXT,
            core_info      TEXT,
            style_str      TEXT,
            string_format  TEXT,
            latex_format   TEXT
            )""")

        # Commit the commands
        conn.commit()

        # Close the connection
        conn.close()

        print("Database now initialized for pkg '{}'.\n".
              format(package_name))

    def insert_record(self, table, record):
        '''
        Insert a single new record (i.e. row) into the specified table
        in the database. The record must be an appropriate-length
        list of attribute values. A ValueError is raised if the table
        is not a valid table in the database or if the list of
        attribute values has the wrong length. Python's None is an
        acceptable value for an attribute that is not declared as NOT
        NULL.
        Catches and returns integrity error information if record
        has a primary key already existing in table.
        '''
        
        # print("Entering the insert_record() method:")
        # print("    with self.full_path_file_name: {}".format(self.full_path_file_name))
        # print("    with record: {}".format(record))
        # print("    with table: {}".format(table))

        # An initial minimal check for problems:
        # is the specified table a valid table in the database?
        if not self._valid_table(table):
            raise ValueError(
                ("Failed attempt to insert a record into the '{0}' table " +
                 "in database '{1}': no such table in the database.").
                format(table, self.file_name))

        conn = sqlite3.connect(self.full_path_file_name)
        c = conn.cursor()

        # Another minimal check for problems:
        # length of record must match number of attributes in table.
        # Get the actual number of attributes in the target table.
        c.execute("SELECT count() FROM PRAGMA_TABLE_INFO('{0}')".format(table))
        # Fetch that selected count.
        num_attributes = c.fetchone()[0]
        # print("    num_attributes = {}".format(num_attributes))
        if num_attributes != len(record):
            raise ValueError(
                ("Failed attempt to insert a record into the '{0}' table " +
                "in database '{1}'. The provided record had {2} " +
                "attributes, whereas the table expected a record "+
                "with {3} attributes.").format(
                    table, self.file_name, len(record), num_attributes ))

        # More sophisticated check might eventually be useful as well:
        # check that each attribute value has the correct type (TBA).

        # use num_attributes to construct the correct execution
        # string for inserting the record
        question_mark_string = '('
        for _i in range(num_attributes-1):
            question_mark_string += '?,'
        question_mark_string = question_mark_string + '?)'

        # Insert attribute values into the specified table
        # Do this inside try/except block to catch a database
        # IntegrityError but still allow the database to be
        # successfully closed afterward.
        try:
            c.execute("INSERT INTO '{0}' VALUES {1}".
                      format(table, question_mark_string),
                      record)
        except Exception as the_exception:
            print("Database Exception: {}".format(the_exception))
            print("Database insertion unsuccessful")

        # Commit the command(s) and close the connection
        conn.commit()
        conn.close()

    def delete_record(self, table, **kwargs):
        '''
        Delete one or more records (i.e. one or more rows) from the
        specified table in the database, identifying the records by the
        conjunction of the table attribute/value kwargs supplied.
        Table attribute names should be specified without quotation
        marks; attribute values should be either NULL or of type
        INTEGER, REAL, or TEXT (i.e. string). For example, in a table
        called 'customers' containing (TEXT) attributes last_name,
        first_name, and (INTEGER) attribute telephone_num, calling the
        following:

            delete_record(
                'customers', last_name='Brown', telephone_num=1234)

        will delete ALL records that have both (i.e. simultanously) a
        last_name attribute of 'Brown' and a telephone_num attribute
        of 1234 in the table 'customers'.
        The table must be an actual table in the database, and all
        attributes must be actual attributes of the table, else a
        ValueError is raised.
        Deleting a non-existent record will NOT raise an error.
        
        '''

        # Check that the kwargs dictionary is not empty:
        if len(kwargs)==0:
            raise ValueError(
                ("Failed attempt to check for record in the '{0}' table " +
                 "in database '{1}': no attribute/value kwargs supplied.").
                format(table, self.file_name))

        # Check: Is the specified table a valid table in the database?
        if not self._valid_table(table):
            raise ValueError(
                ("Failed attempt to delete a record or records from " +
                 "the '{0}' table in database '{1}': " +
                 "no such table in the database.").
                format(table, self.file_name))

        # Check: Are the attributes valid for the table?
        for k in kwargs.keys():
            if not self._valid_attribute(table, k):
                raise ValueError(
                    ("Failed attempt to check for record in the '{0}' table " +
                    "in database '{1}'. The table '{0}' has no attribute " +
                    "'{2}'.").format(table, self.file_name, k))

        # Create the command string.
        command_str = ""
        for idx, (attr,attr_value) in enumerate(kwargs.items()):
            if isinstance(attr_value, str):
                # need to make the quotation marks explicit
                attr_value = "\'" + str(attr_value) + "\'"
            if idx == 0:
                command_str = (
                    ("DELETE FROM {table} " +
                     " WHERE ({attr}={attr_value}").
                     format(table=table, attr=attr,
                           attr_value=attr_value))
            else:
                command_str = (
                    command_str + " AND {attr}={attr_value}".
                    format(attr=attr, attr_value=attr_value))
        command_str = command_str + ")"

        conn = sqlite3.connect(self.full_path_file_name)
        c = conn.cursor()

        # Delete record(s) from the specified table
        c.execute(command_str)
        print("    Deletion raised no fatal errors.")

        # Commit the command(s) and close the connection
        conn.commit()
        conn.close()

    def fetch_all(self, table):
        # Query the db, returning all records in the specified table,
        # in the form of a list of tuples (each tuple corresponding
        # to a record).
        # (Currently a convenience method; to be updated later.)

        # Connect to database
        conn = sqlite3.connect(self.full_path_file_name)
        # Create a cursor
        c = conn.cursor()
        # Query the specified table in the database
        c.execute("SELECT rowid, * FROM " + table) # need to fix
        items = c.fetchall()
        # Close our connection
        conn.close()
        return items

    def check_for_record(self, table, **kwargs):
        '''
        A minimal check for the existence of a record, with one or more
        attributes and corresponding values specified by key word args.
        Returns True if such a record exists and False if not.
        table should be a string specifying a valid table in self.
        Table attribute names should be specified without quotation
        marks; attribute values should be either NULL or of type
        INTEGER, REAL, or TEXT (i.e. string). For example,

            self.check_for_record(
                    'passenger', first_name='Bob', b_year=1961)

        would check the passenger table for an entry where the
        first_name attribute would be the string 'Bob' and the
        b_year attribute would be the integer 1961.
        '''

        # Check that the kwargs dictionary is not empty:
        if len(kwargs)==0:
            raise ValueError(
                ("Failed attempt to check for record in the '{0}' table " +
                 "in database '{1}': no attribute/value kwargs supplied.").
                format(table, self.file_name))

        # Check: Is the specified table a valid table in the database?
        if not self._valid_table(table):
            raise ValueError(
                ("Failed attempt to check for record in the '{0}' table " +
                 "in database '{1}': no such table in the database.").
                format(table, self.file_name))

        # Check: Are the attributes valid for the table?
        for k in kwargs.keys():
            if not self._valid_attribute(table, k):
                raise ValueError(
                    ("Failed attempt to check for record in the '{0}' table " +
                    "in database '{1}'. The table '{0}' has no attribute " +
                    "'{2}'.").format(table, self.file_name, k))

        # Connect to database
        conn = sqlite3.connect(self.full_path_file_name)
        # Create a cursor
        c = conn.cursor()

        # Query the specified table in the database.
        # Here we don't care how many such entries might exist,
        # just if any such entries exist at all.
        query_str = ""
        for idx, (attr,attr_value) in enumerate(kwargs.items()):
            if isinstance(attr_value, str):
                # need to make the quotation marks explicit
                attr_value = "\'" + str(attr_value) + "\'"
            if idx == 0:
                query_str = (
                    ("SELECT EXISTS(SELECT 1 FROM {table} " +
                    " WHERE ({attr}={attr_value}").
                    format(table=table, attr=attr,
                           attr_value=attr_value))
            else:
                query_str = (
                    query_str + " AND {attr}={attr_value}".
                    format(attr=attr, attr_value=attr_value))
        query_str = query_str + "))"

        c.execute(query_str)
        result = c.fetchone()[0]

        # Close our connection
        conn.close

        # finish up
        if result == 1:
            return True
        else:
            return False

    def clear_all_records_in_table(self, table):
        # Clear all records (i.e. rows) in the specified table

        # Connect to database
        conn = sqlite3.connect(self.full_path_file_name)
        # Create a cursor
        c = conn.cursor()
        # Delete all records from the specified table
        c.execute("DELETE FROM " + table)

        # Commit the command(s) and close the connection
        conn.commit()
        conn.close()


    # ==================================== #
    # Utility Functions                    #
    # ==================================== #

    def _get_list_of_tables(self):
        '''
        Return a list of the tables in the database.
        This is useful for raising informative errors, for example
        when a client tries to add a record to a non-existent table.
        '''

        # Connect to the database.
        conn = sqlite3.connect(self.full_path_file_name)
        # Create a cursor
        c = conn.cursor()
        # Obtain the table names (an awkward process)
        c.execute("SELECT name from sqlite_master where type='table'")
        temp_list_of_tuples = c.fetchall()
        # temp_list_of_tuples turns out to be a list of
        # single-element tuples, so we clean things up:
        table_names = []
        for item in temp_list_of_tuples:
            table_names.append(item[0])

        # Close connection and return list of table names
        conn.close()
        return list(table_names)

    def _get_list_of_table_attributes(self, table):
        '''
        Return a list of the attributes in the given table.
        This is useful for raising informative errors, for example
        when a client tries to delete a record by specifying a value
        for an attribute that doesn't exist.
        '''

        # Connect to the database.
        conn = sqlite3.connect(self.full_path_file_name)
        # Create a cursor
        c = conn.cursor()
        # Obtain the attribute names (an awkward process)
        c.execute("SELECT name FROM PRAGMA_TABLE_INFO('{0}')".
                  format(table));
        temp_list_of_tuples = c.fetchall()
        # temp_list_of_tuples turns out to be a list of
        # single-element tuples, so we clean things up:
        attribute_names = []
        for item in temp_list_of_tuples:
            attribute_names.append(item[0])

        # Close connection and return list of attribute names
        conn.close()
        return list(attribute_names)

    def _valid_table(self, table):
        '''
        Return True if table is a valid table in database self,
        else return False.
        '''
        return table in self._get_list_of_tables()

    def _valid_attribute(self, table, attribute):
        '''
        Return True if attribute is a valid attribute for table
        in database self, else return False. Assumes the table itself
        is valid (see _valid_table() method above).
        '''
        return attribute in self._get_list_of_table_attributes(table)

    @staticmethod
    def _parse_unique_rep(unique_rep_str):
        '''
        Given a unique representation string, unique_rep_str, returns
        the list of representations of the referenced Prove-It objects,
        organized based on the type of Prove-It object represented
        by the unique_rep_str.
        '''
        from proveit import Expression, Judgment, Proof

        # ============================================================ #
        # General Processing
        # ============================================================ #

        # split the unique_rep string by semi-colons
        _rep_str_semi_parsed = unique_rep_str.split(";")
        _id_str = _rep_str_semi_parsed[0]
        _reqs_str = _rep_str_semi_parsed[1]
        # then split the first component of that result by the first
        # 2 colons (which avoids splitting on other colons that might
        # appear there in an instantiation's substitution dictionary)

        # Other: Expression
        #   sub-expr, ..., sub-expr; class path; core info; style str 

        # ============================================================ #
        # Proof objects
        # requirement_ids appended w/* are equality requirements?
        # Unique representation strings of Proof objects will have
        # one of the following (string) formats:

        # Proof:assumption:[judgment_id];[]
        # Proof:generalization:[judgment_id];[requirement_ids]
        # Proof:instantiation:{dict}:[judgment_id];[requirement_ids]
        # Proof:modus ponens:[judgment_id];[requirement_ids]
        # Proof:axiom_axiompathname:[judgment_id];[requirement_ids]
        # Proof:theorem_theorempathname:[judgment_id];[requirement_ids]
        #
        # Notice that theorem and axiom objects are actually proof
        # object and have Proof-based unique_rep strings.
        # ============================================================ #

        if unique_rep_str[:5] == 'Proof':
            # print("    Attempting to parse a unique_rep string for a Proof step.")
            _proveit_obj = 'Proof'

            _id_str = _rep_str_semi_parsed[0]
            _mixed_reqs_str = _rep_str_semi_parsed[1].strip("[]")
            # then split the first component of _id_str by the first
            # 2 colons (which avoids splitting on other colons that
            # might appear there in an instantiation's substitution
            # dictionary)
            _id_str_parsed = _id_str.split(":", 2)
            # something strange happening if stripping "[]" produces
            # an empty string, in fact producing an empty tuple, which
            # then behaves weirdly when using split, so we check:
            if len(_mixed_reqs_str) != 0:
                _reqs_str_parsed = _mixed_reqs_str.split(",")
            else:
                _reqs_str_parsed = []

            # process requirements, separating out requirements from
            # equality replacement requirements
            _reqs_list = []
            _eq_replacement_reqs_list = []
            for requirement in _reqs_str_parsed:
                if requirement[-1]=='*':
                    _eq_replacement_reqs_list.append(requirement.strip("*"))
                else:
                    _reqs_list.append(requirement)
            if len(_reqs_list) != 0:
                _reqs_str = "[" + ",".join(_reqs_list) + "]"
            else:
                _reqs_str = None
            if len(_eq_replacement_reqs_list) != 0:
                _eq_replacement_reqs_str = (
                    "[" + ",".join(_eq_replacement_reqs_list) + "]")
            else:
                _eq_replacement_reqs_str = None

            _path_name = None
            _name      = None

            # Proof step: instantiation
            if _id_str_parsed[1] == 'instantiation':
                # then the next piece of str includes a dictionary
                _type = 'instantiation'
                dict_end_idx = _id_str_parsed[2].find("}")
                _subst_dict = _id_str_parsed[2][:dict_end_idx + 1]
                _judgment_id = _id_str_parsed[2][dict_end_idx+1:].strip("[]")
            # then all other types of proof steps
            else:
                _type = _id_str_parsed[1]
                _subst_dict = None
                _judgment_id = _id_str_parsed[2].strip("[]")
                if (_id_str_parsed[1][0:5] == 'axiom' or
                    _id_str_parsed[1][0:7] == 'theorem'):
                    _type = _id_str_parsed[1].split("_", 1)[0]
                    _path_name = _id_str_parsed[1].split("_", 1)[1]
                    _name = _id_str_parsed[1].rsplit(".", 1)[1]
                # else:
                #     _path_name = None
                #     _name = None

            return {'obj':_proveit_obj, 'type':_type, 'subst_dict':_subst_dict,
                    'judgment_id':_judgment_id, 'reqs':_reqs_str,
                    'eq_reqs':_eq_replacement_reqs_str,
                    'path_name': _path_name, 'name':_name}

        # ============================================================ #
        # Judgment objects
        # unique_rep strings of Judgment objects will have
        # the following string format:
        #
        #     'Judgment:expr_id;[assump_id_1, ..., assump_id_n]m'
        #
        # where m is the non-zero number of literal generalizations
        # (when m=0, the most common case, the value is omitted).
        # ============================================================ #

        elif unique_rep_str[:8] == 'Judgment':
            # print("    Attempting to parse a unique_rep string for a Judgment.")
            _proveit_obj = 'Judgment'
            _id_str = _rep_str_semi_parsed[0]     # 'Judgment:expr_id'
            _expr_id = _id_str.split(":")[1]      #          'expr_id'
            if _rep_str_semi_parsed[1][-1]==']':
                _assumptions_str = _rep_str_semi_parsed[1]
                _num_lit_gens = 0
            else:
                assump_end_idx = _rep_str_semi_parsed[1].find("}")
                _assumptions_str = _rep_str_semi_parsed[1][:assump_end_idx+1]
                _num_lit_gens = int(_rep_str_semi_parsed[1][assump_end_idx+1:])
            return {'obj':_proveit_obj,
                    'expr':_expr_id,
                    'assumptions':_assumptions_str,
                    'num_lit_gens':_num_lit_gens}

        # ============================================================ #
        # Expression objects
        # unique_rep strings of Expression objects will have
        # the following string format:
        #
        #     'sub_expr_info;class_path;core_info;style_str'
        #
        # For example, we might have something like this example
        # pulled (and slightly abbreviated) from the
        # physics.quantum.QPE pkg (breaking the string at commas and
        # semicolons to fit in this space):
        #
        #    proveit.logic.booleans.....common.083d2...,
        #    49c89bde7b2e90ddc64350c8088ab9227170dd910;  
        #    proveit.logic.booleans.....forall.Forall;
        #    Operation;
        #    with_wrapping:True
        #
        # Notice also that the core_info entry always ends with a
        # semi-colon, so splitting the string on ";" always produces
        # a 4th entry, though sometimes the entry is the empty string.
        # ============================================================ #

        else:
            # Assumed to be an Expression
            _proveit_obj = 'Expression'
            _sub_exprs  = '[' + _rep_str_semi_parsed[0] + ']'
            _class_path = _rep_str_semi_parsed[1]
            _core_info  = _rep_str_semi_parsed[2]
            _style_str  = _rep_str_semi_parsed[3]
            if _style_str == '':
                # The None Python type will automatically convert to the
                # desired NULL when storing into sqlite database
                _style_str = None
            return {'obj':_proveit_obj,
                    'sub_exprs':_sub_exprs,
                    'class_path':_class_path,
                    'core_info':_core_info,
                    'style_str':_style_str}
